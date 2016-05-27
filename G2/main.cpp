//Maciej Poleski
//#define DEBUG
#ifndef DEBUG
#define NDEBUG
#else
#define _GLIBCXX_CONCEPT_CHECKS
#endif

#include <iostream>
#include <vector>
#include <algorithm>
#include <iomanip>
#include <cassert>
#include <unordered_map>
#include <map>
#include <set>
#include <unistd.h>
#include <fcntl.h>
#include <functional>
#include <unordered_set>
#include <csignal>
#include <list>
#include <utility>
#include <memory>
#include <tuple>

#include <CGAL/Exact_predicates_inexact_constructions_kernel.h>
#include <CGAL/Triangulation_vertex_base_with_info_2.h>
#include <CGAL/Point_set_2.h>
#include <CGAL/convex_hull_2.h>
#include <CGAL/Point_2.h>
#include <CGAL/Polytope_distance_d_traits_2.h>
#include <CGAL/Polytope_distance_d.h>

using namespace std;

class FindUnion
{
    vector<int> parent;
    vector<int> rank;

public:
    FindUnion(int n);

    bool tryUnion(int a, int b);

    int find(int a);
};

FindUnion::FindUnion(int n) : parent(n), rank(n)
{
    for (int i = 0; i < n; ++i)
        parent[i] = i;
}

bool FindUnion::tryUnion(int a, int b)
{
    a = find(a);
    b = find(b);
    if (a == b) {
        return false;
    }
    if (rank[a] > rank[b]) {
        swap(a, b);
    }
    // rank[b] >= rank[a]
    parent[a] = b;
    if (rank[a] == rank[b]) {
        rank[b] += 1;
    }
    return true;
}

int FindUnion::find(int a)
{
    if (parent[a] == a) {
        return a;
    }
    return parent[a] = find(parent[a]);
}

template<typename Integer>
class SplayTree
{
public:
    struct Node
    {
        Integer parent;
        Integer left, right;
        bool reversed;
    };

public:
    static constexpr Integer null = numeric_limits<Integer>::max();

    template<typename Iterator>
    // RandomAccessIterator
    SplayTree(Iterator begin, Iterator end);

    Integer before(Integer vertex);

    Integer after(Integer vertex);

    vector<Integer> dumpOrderly() const;

    void moveToEnd(Integer vertex);

    void reverseAfter(Integer vertex);

    void cyclicRotateToEnd(Integer vertex);

    Integer first() const
    {
        return first(root);
    }

    Integer last() const
    {
        return last(root);
    }

private:
    vector<Node> chunk;
    Integer root;

    void dispatchReversal(Integer vertex);

    Integer &left(Integer v)
    {
        assert(v != null);
        return chunk[v].left;
    }

    Integer left(Integer v) const
    {
        return const_cast<SplayTree *>(this)->left(v);
    }

    Integer &right(Integer v)
    {
        assert(v != null);
        return chunk[v].right;
    }

    Integer right(Integer v) const
    {
        return const_cast<SplayTree *>(this)->right(v);
    }

    Integer &parent(Integer v)
    {
        assert(v != null);
        return chunk[v].parent;
    }

    Integer parent(Integer v) const
    {
        return const_cast<SplayTree *>(this)->parent(v);
    }

    bool &reversed(Integer v)
    {
        assert(v != null);
        return chunk[v].reversed;
    }

    bool reversed(Integer v) const
    {
        return const_cast<SplayTree *>(this)->reversed(v);
    }

    bool isParent(Integer p, Integer chld)
    {
        if (p == null) {
            return (root == chld) && (parent(chld) == p);
        }
        return ((chld == null) || (parent(chld) == p)) && ((left(p) == chld) || (right(p) == chld));
    }

    void setLeftChild(Integer v, Integer child)
    {
        assert(v != null);
        left(v) = child;
        if (child != null) {
            parent(child) = v;
        }
        assert(isParent(v, child));
    }

    void setRightChild(Integer v, Integer child)
    {
        assert(v != null);
        right(v) = child;
        if (child != null) {
            parent(child) = v;
        }
        assert(isParent(v, child));
    }

    void substituteChild(Integer v, Integer oldChild, Integer newChild)
    {
        if (v == null) {
            assert(root == oldChild);
            parent(newChild) = null;
            root = newChild;
        } else if (left(v) == oldChild) {
            setLeftChild(v, newChild);
        } else {
            assert(right(v) == oldChild);
            setRightChild(v, newChild);
        }
    }

    void zig(Integer x);

    void zigZig(Integer x);

    void zigZag(Integer x);

    void splay(Integer vertex);

    Integer first(Integer v) const;

    Integer last(Integer v) const;
};

// Ustawia left, right, reversed. Nie ustawia parent
template<typename Iterator>
static typename iterator_traits<Iterator>::value_type
buildStructure(vector<typename SplayTree<typename iterator_traits<Iterator>::value_type>::Node> &chunk, Iterator begin,
               Iterator end)
{
    // Iterator powinien być RandomAccessIterator, w przeciwnym wypadku - gorsza złożoność
    typedef typename iterator_traits<Iterator>::value_type Integer;
    assert(begin <= end);
    if (begin == end) {
        return SplayTree<Integer>::null;
    } else if (begin + 1 == end) {
        chunk[*begin].left = chunk[*begin].right = SplayTree<Integer>::null;
        chunk[*begin].reversed = false;
        return *begin;
    }
    Iterator center = begin + (distance(begin, end) / 2);
    auto left = chunk[*center].left = buildStructure(chunk, begin, center);
    auto right = chunk[*center].right = buildStructure(chunk, center + 1, end);
    if (left != SplayTree<Integer>::null) {
        chunk[left].parent = *center;
    }
    if (right != SplayTree<Integer>::null) {
        chunk[right].parent = *center;
    }
    assert(chunk[*center].left != *center);
    assert(chunk[*center].right != *center);
    return *center;
}

template<typename Integer>
template<typename Iterator>
SplayTree<Integer>::SplayTree(Iterator begin, Iterator end) : chunk(*max_element(begin, end) + 1)
{
    root = buildStructure(chunk, begin, end);
    parent(root) = null;
#ifdef TEST_SPLAY
    for (int i = 0; i < n; ++i) {
        assert(isParent(parent(i), i));
        assert(isParent(i, left(i)));
        assert(isParent(i, right(i)));
    }
#endif
}

template<typename Integer>
Integer SplayTree<Integer>::before(Integer vertex)
{
    splay(vertex);
    assert(!reversed(vertex));
    if (left(vertex) == null) {
        return null;
    }
    return last(left(vertex));
}

// co szkodziłoby zrobić before zakładając wstępnie że reversed?
template<typename Integer>
Integer SplayTree<Integer>::after(Integer vertex)
{
    splay(vertex);
    assert(!reversed(vertex));
    if (right(vertex) == null) {
        return null;
    }
    return first(right(vertex));
}

template<typename Integer>
static void
dumpSplayChunk(const vector<typename SplayTree<Integer>::Node> &chunk, Integer v, bool reverse, vector<Integer> &order)
{
    if (v == SplayTree<Integer>::null) {
        return;
    }
    reverse = (reverse != chunk[v].reversed);
    if (reverse) {
        dumpSplayChunk(chunk, chunk[v].right, reverse, order);
        order.push_back(v);
        dumpSplayChunk(chunk, chunk[v].left, reverse, order);
    } else {
        dumpSplayChunk(chunk, chunk[v].left, reverse, order);
        order.push_back(v);
        dumpSplayChunk(chunk, chunk[v].right, reverse, order);
    }
}

template<typename Integer>
vector<Integer> SplayTree<Integer>::dumpOrderly() const
{
    vector<Integer> result;
    dumpSplayChunk(chunk, root, false, result);
    return result;
}

template<typename Integer>
void SplayTree<Integer>::moveToEnd(Integer vertex)
{
#ifdef TEST_SPLAY
    auto oldOrder = dumpOrderly();
#endif
    auto prev = before(vertex);
    // wykonano splay na vertex - vertex jest w korzeniu
    assert(!reversed(vertex));
    if (prev != null) {
        root = left(vertex);
        assert(root != null); // skoro jest poprzednik to musi coś być z lewej strony
        parent(root) = null;
        left(vertex) = null;
        // lewe poddrzewo vertex odcięte
        splay(prev);
        assert(right(prev) == null); // zwolnione miejsce z prawej strony prev
        setRightChild(prev, vertex);
    }
    reversed(vertex) = true;
    if (right(vertex) != null) {
        reversed(right(vertex)) = !reversed(right(vertex));
    }
#ifdef TEST_SPLAY
    auto newOrder = dumpOrderly();
    oldOrder.erase(find(oldOrder.begin(), oldOrder.end(), vertex));
    oldOrder.push_back(vertex);
    assert(oldOrder == newOrder);
#endif
}

template<typename Integer>
void SplayTree<Integer>::reverseAfter(Integer vertex)
{
#ifdef TEST_SPLAY
    auto oldOrder = dumpOrderly();
#endif
    splay(vertex);
    assert(!reversed(vertex));
    auto r = right(vertex);
    if (r != null) {
        reversed(r) = !reversed(r);
    }
#ifdef TEST_SPLAY
    auto newOrder = dumpOrderly();
    reverse(find(oldOrder.begin(), oldOrder.end(), vertex) + 1, oldOrder.end());
    assert(oldOrder == newOrder);
#endif
}

template<typename Integer>
void SplayTree<Integer>::cyclicRotateToEnd(Integer vertex)
{
#ifdef TEST_SPLAY
    long oldLength;
    {
        auto oldOrder = dumpOrderly();
        oldLength = getHamiltonianLength(oldOrder.begin(), oldOrder.end());
    };
#endif
    splay(vertex);
    assert(root == vertex);
    assert(!reversed(root));
    if (right(root) == null) {
        return; // vertex już na końcu
    }
    auto f = first();
    auto r = right(root);
    bool needReverse = false;
    for (auto i = f; i != root; i = parent(i))
        needReverse = (needReverse != reversed(i));
    right(root) = null;
    if (needReverse) {
        assert(right(f) == null);
        setRightChild(f, r);
    } else {
        assert(left(f) == null);
        setLeftChild(f, r);
    }
    reversed(r) = (reversed(r) != needReverse);
#ifdef TEST_SPLAY
    long newLength;
    {
        auto newOrder = dumpOrderly();
        newLength = getHamiltonianLength(newOrder.begin(), newOrder.end());
    };
    assert(oldLength == newLength);
#endif
}

template<typename Integer>
void SplayTree<Integer>::dispatchReversal(Integer vertex)
{
    if (reversed(vertex)) {
        reversed(vertex) = false;
        assert(reversed(vertex) == false);
        swap(left(vertex), right(vertex));
        if (left(vertex) != null) {
            reversed(left(vertex)) = !reversed(left(vertex));
        }
        if (right(vertex) != null) {
            reversed(right(vertex)) = !reversed(right(vertex));
        }
    }
}

template<typename Integer>
void SplayTree<Integer>::zig(Integer x)
{
    assert(x < chunk.size());
    Integer p = parent(x);
    assert(p < chunk.size());
    assert(parent(p) == null);
    assert(root == p);
    assert(!reversed(p));
    assert(!reversed(x));
    if (left(p) == x) { // wiki wariant
        auto b = right(x);
        setRightChild(x, p);
        setLeftChild(p, b);
        assert(isParent(p, b));
    } else { // odwrócony wiki wariant
        auto b = left(x);
        setLeftChild(x, p);
        setRightChild(p, b);
        assert(isParent(p, b));
    }
    parent(x) = null;
    root = x;
    assert(isParent(x, p));
    assert(isParent(null, x));
}

template<typename Integer>
void SplayTree<Integer>::zigZig(Integer x)
{
    assert(x < chunk.size());
    Integer p = parent(x);
    assert(p < chunk.size());
    Integer g = parent(p);
    assert(g < chunk.size());
    assert(!reversed(g));
    assert(!reversed(p));
    assert(!reversed(x));
    assert(((left(g) == p) && (left(p) == x)) || ((right(g) == p) && (right(p) == x)));
    auto gparent = parent(g);
    if (left(p) == x) { // wiki wariant
        auto b = right(x);
        auto c = right(p);
        setLeftChild(g, c);
        setLeftChild(p, b);
        setRightChild(p, g);
        setRightChild(x, p);
        assert(isParent(p, b));
        assert(isParent(g, c));
    } else { // odwrócony wiki wariant
        auto b = left(p);
        auto c = left(x);
        setRightChild(g, b);
        setRightChild(p, c);
        setLeftChild(p, g);
        setLeftChild(x, p);
        assert(isParent(g, b));
        assert(isParent(p, c));
    }
    substituteChild(gparent, g, x);
    assert(isParent(x, p));
    assert(isParent(p, g));
    assert(isParent(gparent, x));
}

template<typename Integer>
void SplayTree<Integer>::zigZag(Integer x)
{
    assert(x < chunk.size());
    Integer p = parent(x);
    assert(p < chunk.size());
    Integer g = parent(p);
    assert(g < chunk.size());
    assert(!reversed(g));
    assert(!reversed(p));
    assert(!reversed(x));
    assert(((left(g) == p) && (right(p) == x)) || ((right(g) == p) && (left(p) == x)));
    auto gparent = parent(g);
    if (right(p) == x) { // wiki wariant
        auto b = left(x);
        auto c = right(x);
        setRightChild(p, b);
        setLeftChild(g, c);
        setLeftChild(x, p);
        setRightChild(x, g);
        assert(isParent(p, b));
        assert(isParent(g, c));
    } else { // odwrócony wiki wariant
        auto b = left(x);
        auto c = right(x);
        setRightChild(g, b);
        setLeftChild(p, c);
        setLeftChild(x, g);
        setRightChild(x, p);
        assert(isParent(g, b));
        assert(isParent(p, c));
    }
    substituteChild(gparent, g, x);
    assert(isParent(x, p));
    assert(isParent(x, g));
    assert(isParent(gparent, x));
}

template<typename Integer>
void SplayTree<Integer>::splay(Integer vertex)
{
    assert(vertex != null);
#ifdef TEST_SPLAY
    auto oldOrder = dumpOrderly();
#endif
    while (parent(vertex) != null) {
        auto p = parent(vertex);
        assert(isParent(p, vertex));
        if (parent(p) == null) {
            dispatchReversal(p);
            dispatchReversal(vertex);
            zig(vertex);
        } else {
            auto g = parent(p);
            assert(isParent(g, p));
            dispatchReversal(g);
            dispatchReversal(p);
            dispatchReversal(vertex);
            if ((left(p) == vertex) == (left(g) == p)) {
                zigZig(vertex);
            } else {
                zigZag(vertex);
            }
        }
    }
    assert(root == vertex);
    dispatchReversal(root); // błędnie założyłem że splay zawsze pozostawia korzeń oczyszczony z reversed
    assert(!reversed(root));
#ifdef TEST_SPLAY
    auto newOrder = dumpOrderly();
    assert(oldOrder == newOrder);
#endif
}

template<typename Integer>
Integer SplayTree<Integer>::first(Integer vertex) const
{
    auto i = vertex;
    bool rev = false;
    for (auto next = i; next != null;) {
        i = next;
        rev = (rev != reversed(i));
        if (rev) {
            next = right(i);
        } else {
            next = left(i);
        }
    }
    return i;
}

template<typename Integer>
Integer SplayTree<Integer>::last(Integer vertex) const
{
    auto i = vertex;
    bool rev = false;
    for (auto next = i; next != null;) {
        i = next;
        rev = (rev != reversed(i));
        if (rev) {
            next = left(i);
        } else {
            next = right(i);
        }
    }
    return i;
}

/******************* ROZWIĄZANIE *****************/

//jądro obliczeń arytmetyczych
typedef CGAL::Exact_predicates_inexact_constructions_kernel K;

//opisy wierzchołków
typedef CGAL::Triangulation_vertex_base_with_info_2<int, K> Vb;

//reprezentacja triangulacji (ściany i wierzchołki)
typedef CGAL::Triangulation_data_structure_2<Vb> Tds;

//reprezentacja grafu Delaunaya
//Point_set_2 jest klasą potomną Delaunay_triangulation_2
//zawierającą dodatkowe metody, m.in. nearest_neighbors()
typedef CGAL::Point_set_2<K, Tds> Delaunay;

typedef Delaunay::Point Point;                 //punkt grafu Delaunay'a
typedef Delaunay::Edge_iterator Edge_iterator; //iterator po krawedziach grafu Delaunaya
typedef Delaunay::Vertex_handle Vertex_handle; //iterator po punktach grafu Delaunaya

static int n;
static vector<Point> input;
static vector<vector<int>> G;   // graf kandydatów
static vector<vector<int>> Gcells; // wszystkie grafy kandydatów komórek

static double dist(int v, int w)
{
    double x = input[v].x() - input[w].x();
    double y = input[v].y() - input[w].y();
//    return hypot(x, y);
    return sqrt(x * x + y * y);
}

//#if 0
static int euclid(int v, int w)
{
    return static_cast<int>(dist(v, w) + 0.5);
}
//#endif

//static int euclid(Point A, Point B)
//{
//    double x = A.x() - B.x();
//    double y = A.y() - B.y();
//    return static_cast<int>(hypot(x, y) + .5);
//}

static void buildG()
{
    const int nbNeighbors = 10;
    G.resize(n);
    Delaunay D;
    vector<pair<Point, int>> delonePoints;
    assert(input.size() == n);
    for (int i = 0; i < n; ++i) {
        delonePoints.push_back(make_pair(input[i], i));
    }
    D.insert(delonePoints.begin(), delonePoints.end());
    vector<unordered_set<int>> Gproto(n);
    for (auto i = D.finite_vertices_begin(), e = D.finite_vertices_end(); i != e; ++i) {
        vector<int> neighbors;
        auto vc = i->incident_vertices();
        CGAL::Container_from_circulator<decltype(vc)> c(vc);
        for (auto &v : c) {
            if (!D.is_infinite(v.handle())) {
                neighbors.push_back(v.info());
            }
        }
        vector<Vertex_handle> near;
        D.nearest_neighbors(i, 1 + nbNeighbors, back_inserter(near));
        assert(near.size() >= min(nbNeighbors, n - 1));
        for (auto &v : near) {
            if ((!D.is_infinite(v)) && (v != i->handle())) {
                neighbors.push_back(v->info());
            }
        }
        assert(neighbors.size() >= min(nbNeighbors, n - 1));
        Gproto[i->info()].insert(neighbors.begin(), neighbors.end());
        for (auto &v:neighbors) {
            Gproto[v].insert(i->info());
        }
    }
    for (int i = 0; i < n; ++i) {
#ifdef DEBUG
        for (auto &v:Gproto[i]) {
            assert(Gproto[v].find(i) != Gproto[v].end());
        }
#endif
        G[i].assign(Gproto[i].begin(), Gproto[i].end());
        assert(G[i].size() >= min(nbNeighbors, n - 1));
    }
}

namespace std {
    template<>
    struct hash<pair<int, int>>
    {
        size_t operator()(const pair<int, int> &p) const noexcept
        {
            return size_t(p.first) << 32 | size_t(p.second);
        }
    };
}

namespace std {
    template<>
    struct hash<Point>
    {
        size_t operator()(const Point &p) const noexcept
        {
            hash<double> h;
            return (h(p.x()) << 1) ^ h(p.y());
        }
    };
}

static mt19937 randomEngine(time(0));

template<class ForwardIterator>
static long getHamiltonianLength(ForwardIterator begin, ForwardIterator end)
{
    long result = 0;
    ForwardIterator j = begin, i = j++;
    for (; j < end; ++i, ++j) {
        result += euclid(*i, *j);
    }
    result += euclid(*i, *begin);
    return result;
}


template<typename DContainer, typename SContainer>
void copy(DContainer &dest, const SContainer &source)
{
    copy(source.begin(), source.end(), back_inserter(dest));
};

static pair<double, vector<int16_t>>
compute1TreeOnCandidates(const vector<double> &P, vector<pair<uint16_t, uint16_t>> &edges)
{
    sort(edges.begin(), edges.end(), [&P](pair<uint16_t, uint16_t> lhs, pair<uint16_t, uint16_t> rhs) {
        return euclid(lhs.first, lhs.second) + P[lhs.first] + P[lhs.second] <
               euclid(rhs.first, rhs.second) + P[rhs.first] + P[rhs.second];
    });
    vector<int16_t> newD(n, -2);
    vector<uint16_t> boundTo(n); // parent dla liści
    double weight = 0;
    FindUnion findUnion(n);
    auto components = n;
    for (auto e : edges) {
        auto u = e.first;
        auto v = e.second;
        if (findUnion.tryUnion(u, v)) {
            components -= 1;
            newD[u] += 1;
            newD[v] += 1;
            boundTo[u] = v;
            boundTo[v] = u;
            weight += euclid(u, v) + P[u] + P[v];
            if (components == 1) {
                break;
            }
        }
    }
    pair<int, int> oneEdge;
    double oneEdgeWeight = -1;
    for (int u = 0; u < n; ++u) {
        if (newD[u] != -1) {
            continue;
        }
        int currentV;
        double currentWeight = numeric_limits<double>::max();
        for (auto v : G[u]) {
            if (v == boundTo[u]) {
                continue;
            }
            auto weight = euclid(u, v) + P[u] + P[v];
            if (weight < currentWeight) {
                currentV = v;
                currentWeight = weight;
            }
        }
        assert(currentWeight != numeric_limits<double>::max());
        if (oneEdgeWeight < currentWeight) {
            oneEdgeWeight = currentWeight;
            oneEdge = {u, currentV};
        }
    }
    assert(oneEdgeWeight > 0);
    newD[oneEdge.first] += 1;
    newD[oneEdge.second] += 1;
    weight += oneEdgeWeight;
    return {weight, move(newD)};
};

static pair<double, vector<int16_t>> compute1TreeOnEuclidean(const vector<double> &P)
{
    vector<pair<uint16_t, uint16_t>> edges;
    edges.reserve(n * (n - 1) / 2);
    for (int u = 0; u < n; ++u) {
        for (int v = u + 1; v < n; ++v) {
            edges.emplace_back(u, v);
        }
    }
    sort(edges.begin(), edges.end(), [&P](pair<uint16_t, uint16_t> lhs, pair<uint16_t, uint16_t> rhs) {
        return euclid(lhs.first, lhs.second) + P[lhs.first] + P[lhs.second] <
               euclid(rhs.first, rhs.second) + P[rhs.first] + P[rhs.second];
    });
    vector<int16_t> newD(n, -2);
    vector<uint16_t> boundTo(n); // parent dla liści
    double weight = 0;
    FindUnion findUnion(n);
    auto components = n;
    for (auto e : edges) {
        auto u = e.first;
        auto v = e.second;
        if (findUnion.tryUnion(u, v)) {
            components -= 1;
            newD[u] += 1;
            newD[v] += 1;
            boundTo[u] = v;
            boundTo[v] = u;
            weight += euclid(u, v) + P[u] + P[v];
            if (components == 1) {
                break;
            }
        }
    }
    pair<int, int> oneEdge;
    double oneEdgeWeight = -1;
    for (int u = 0; u < n; ++u) {
        if (newD[u] != -1) {
            continue;
        }
        int currentV;
        double currentWeight = numeric_limits<double>::max();
        for (int v = 0; v < n; ++v) {
            if (v == u || v == boundTo[u]) {
                continue;
            }
            auto weight = euclid(u, v) + P[u] + P[v];
            if (weight < currentWeight) {
                currentV = v;
                currentWeight = weight;
            }
        }
        assert(currentWeight != numeric_limits<double>::max());
        if (oneEdgeWeight < currentWeight) {
            oneEdgeWeight = currentWeight;
            oneEdge = {u, currentV};
        }
    }
    assert(oneEdgeWeight > 0);
    newD[oneEdge.first] += 1;
    newD[oneEdge.second] += 1;
    weight += oneEdgeWeight;
    return {weight, move(newD)};
}

static pair<vector<uint16_t>,long> buildHamiltonianFromMst(vector<list < uint16_t>> &&MST)
{
    list <uint16_t> verticesWithDegree1or0;
    for (int u = 0; u < n; ++u) {
        if (MST[u].size() == 1) {
            verticesWithDegree1or0.push_back(u);
        }
    }
    vector<uint16_t> result;
    vector<bool> removed(n, false);
    long resultLength = 0;
    result.reserve(n);
    while (!verticesWithDegree1or0.empty()) {
        auto u = verticesWithDegree1or0.back();
        verticesWithDegree1or0.pop_back();
        if (removed[u]) {
            continue;
        }
        removed[u] = true;
        result.push_back(u);
        if (verticesWithDegree1or0.empty()) {
            break;
        }
        // walk and extract
        auto bestPosition = MST[u].end();
        int bestPositionDistance = numeric_limits<int>::max();
        for (auto i = MST[u].begin(), e = MST[u].end(); i != e; ++i) {
            if (bestPositionDistance > euclid(u, *i)) {
                bestPositionDistance = euclid(u, *i);
                bestPosition = i;
            }
        }
        uint16_t v;
        if (bestPosition != MST[u].end()) {
            v = *bestPosition;
            resultLength += bestPositionDistance;
        } else {
            // znajdź nowy początek
            assert(!verticesWithDegree1or0.empty());
            auto bestPosition = verticesWithDegree1or0.end();
            int bestPositionDistance = numeric_limits<int>::max();
            for (auto i = verticesWithDegree1or0.begin(), e = verticesWithDegree1or0.end(); i != e; ++i) {
                if (removed[*i]) {
                    continue; // TODO można przyspieszyć
                }
                if (bestPositionDistance > euclid(u, *i)) {
                    bestPositionDistance = euclid(u, *i);
                    bestPosition = i;
                }
            }
            //assert(bestPosition != verticesWithDegree1or0.end());
            if(bestPosition == verticesWithDegree1or0.end()) {
                break;
            }
            v = *bestPosition;
            verticesWithDegree1or0.erase(bestPosition);
            resultLength += bestPositionDistance;
        }
        for (auto x : MST[u]) {
            MST[x].erase(find(MST[x].begin(), MST[x].end(), u));
            if(MST[x].size() == 1) {
                verticesWithDegree1or0.push_back(x);
            }
        }
        MST[u].clear();
        verticesWithDegree1or0.push_back(v); // wybrany liść lub wierzchołek wewnętrzny
    }
    resultLength += euclid(result[0], result.back());
    return {move(result), resultLength};
}

static tuple<double, vector<int16_t>, pair<vector<uint16_t>,long>>
compute1TreeAndSolutionOnCandidates(const vector<double> &P, vector<pair<uint16_t, uint16_t>> &edges)
{
    sort(edges.begin(), edges.end(), [&P](pair<uint16_t, uint16_t> lhs, pair<uint16_t, uint16_t> rhs) {
        return euclid(lhs.first, lhs.second) + P[lhs.first] + P[lhs.second] <
               euclid(rhs.first, rhs.second) + P[rhs.first] + P[rhs.second];
    });
    vector<list < uint16_t>> MST(n);
    double weight = 0;
    FindUnion findUnion(n);
    auto components = n;
    for (auto e : edges) {
        auto u = e.first;
        auto v = e.second;
        if (findUnion.tryUnion(u, v)) {
            components -= 1;
            MST[u].push_back(v);
            MST[v].push_back(u);
            weight += euclid(u, v) + P[u] + P[v];
            if (components == 1) {
                break;
            }
        }
    }
    vector<int16_t> newD(n);
    for (int i = 0; i < n; ++i) {
        newD[i] = static_cast<int16_t>(MST[i].size()) - 2;
    }
    pair<int, int> oneEdge;
    double oneEdgeWeight = -1;
    for (int u = 0; u < n; ++u) {
        if (newD[u] != -1) {
            continue;
        }
        int currentV;
        double currentWeight = numeric_limits<double>::max();
        for (auto v : G[u]) {
            if (v == MST[u].front()) {
                continue;
            }
            auto weight = euclid(u, v) + P[u] + P[v];
            if (weight < currentWeight) {
                currentV = v;
                currentWeight = weight;
            }
        }
        assert(currentWeight != numeric_limits<double>::max());
        if (oneEdgeWeight < currentWeight) {
            oneEdgeWeight = currentWeight;
            oneEdge = {u, currentV};
        }
    }
    assert(oneEdgeWeight > 0);
    newD[oneEdge.first] += 1;
    newD[oneEdge.second] += 1;
    weight += oneEdgeWeight;
    return make_tuple(weight, move(newD), buildHamiltonianFromMst(move(MST)));
};

int main()
{
    //close(0);
    //open("/home/local/AA/G2/testy/55.in", O_RDONLY);
    ios_base::sync_with_stdio(false);
    int z;
    cin >> z;
    while (z--) {
        cin >> n;
        input.resize(n);
        for (auto &p:input) {
            cin >> p;
        }
        buildG();
        long upperBound = euclid(0, n - 1);
        for (int v = 1; v < n; ++v) {
            upperBound += euclid(v - 1, v);
        }
        vector<pair<uint16_t, uint16_t>> edges;
        for (uint16_t u = 0; u < n; ++u) {
            for (uint16_t v : G[u]) {
                if (u < v) {
                    edges.emplace_back(u, v);
                }
            }
        }
        const double lambda = 0.98;
        vector<double> P(n);
        vector<double> bestP;
        double bestPValue = 0;
        vector<int16_t> oldD(n);
        double step = -1;
        for (int iteration = 0; iteration < 350; ++iteration) {
            auto oneTree = compute1TreeOnCandidates(P, edges);
            if (oneTree.first > bestPValue) {
                bestPValue = oneTree.first;
                bestP = P;
            }
            if (step == -1) {
                step = (upperBound - oneTree.first) / static_cast<double>(n);
                for (int i = 0; i < n; ++i) {
                    P[i] += step * (oneTree.second[i]);
                }
            } else {
                step = step * lambda;
                for (int i = 0; i < n; ++i) {
                    P[i] += step * (0.7 * oneTree.second[i] + 0.3 * oldD[i]);
                }
            }
            oldD = move(oneTree.second);
        }
        pair<vector<uint16_t>,long> bestHamiltonian = {{},numeric_limits<long>::max()};
        for (int iteration = 350; iteration < 500; ++iteration) {
            auto oneTreeAndSolution = compute1TreeAndSolutionOnCandidates(P, edges);
            if (get<0>(oneTreeAndSolution) > bestPValue) {
                bestPValue = get<0>(oneTreeAndSolution);
                bestP = P;
            }
            step = step * lambda;
            for (int i = 0; i < n; ++i) {
                P[i] += step * (0.7 * get<1>(oneTreeAndSolution)[i] + 0.3 * oldD[i]);
            }
            oldD = move(get<1>(oneTreeAndSolution));
            if(get<2>(oneTreeAndSolution).second<bestHamiltonian.second) {
#ifdef DEBUG
                assert(get<2>(oneTreeAndSolution).second == getHamiltonianLength(get<2>(oneTreeAndSolution).first.begin(), get<2>(oneTreeAndSolution).first.end()));
#endif
                bestHamiltonian = move(get<2>(oneTreeAndSolution));
            }
        }
        auto realOneTree = compute1TreeOnEuclidean(bestP);
        cout << static_cast<long>(realOneTree.first - 2 * accumulate(bestP.begin(), bestP.end(), .0) + .5) << '\n';
        for(auto v : bestHamiltonian.first) {
            cout << v << ' ';
        }
        cout << '\n' << bestHamiltonian.second << '\n';
    }
    return 0;
}