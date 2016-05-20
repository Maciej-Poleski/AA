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
static typename iterator_traits<Iterator>::value_type buildStructure(
        vector<typename SplayTree<typename iterator_traits<Iterator>::value_type>::Node> &chunk, Iterator begin,
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
static void dumpSplayChunk(const vector<typename SplayTree<Integer>::Node> &chunk, Integer v, bool reverse,
                           vector<Integer> &order)
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

typedef uint_fast8_t metaCoord_t;
typedef pair<metaCoord_t, metaCoord_t> metaCoords_t;

class PlaneHierarchy
{
    class PlaneCell
    {
        vector<int> points;
        vector<int> convexHull; // użyte podczas szukania ścieżek w komórkach i przy wyznaczaniu odległości między komórkami
        Point representant;
    public:
        void addPoint(int p)
        {
            points.push_back(p);
        }

        void construct()
        {
            chooseRepresentantPoint();
            computeCandidates();
        }

        Point getRepresentant() const
        {
            return representant;
        }

        const vector<int> &getPoints() const
        {
            return points;
        }

        const vector<int> &getConvexHull() const
        {
            return convexHull;
        }

        bool empty() const
        {
            return points.empty();
        }

    private:
        void chooseRepresentantPoint();

        void computeCandidates();
    };

    struct CellRelative
    {
        int distance = -1;
        int from, to;   // Identyfikator globalny (nie points-iterator)
    };

    vector<PlaneCell> cells;
    vector<CellRelative> distances;
    vector<metaCoords_t> pointToCell;
    int k;

public:
    PlaneHierarchy(int k);

    int euclid(metaCoords_t A, metaCoords_t B);

    vector<metaCoords_t> chooseMetaCycle();

    vector<int> choosePathForChunk(metaCoords_t before, metaCoords_t chunk, metaCoords_t after);

    int encode(metaCoords_t P) const
    {
        return encode(P.first, P.second);
    }

private:
    int encode(int x, int y) const
    {
        assert(x >= 0);
        assert(y >= 0);
        assert(x * k + y < k * k);
        return y * k + x;
    }

    metaCoords_t fixCellAddress(int x, int y) const;

    metaCoords_t decode(int code) const
    {
        return {code % k, code / k};
    }

    PlaneCell &getCell(int code)
    {
        assert(code >= 0);
        assert(code < cells.size());
        return cells[code];
    }

    PlaneCell &getCell(int x, int y)
    {
        return cells[encode(x, y)];
    }

    PlaneCell &getCell(metaCoords_t p)
    {
        return getCell(p.first, p.second);
    }

    // round edges
    PlaneCell &getCellChecked(int x, int y)
    {
        return getCell(fixCellAddress(x, y));
    }

    int encodeMeta(metaCoords_t A, metaCoords_t B) const
    { return encode(B) * k * k + encode(A); }

    vector<metaCoords_t> optimized(list <metaCoords_t> &&path);

    vector<int> optimized(metaCoords_t chunk, list<int> &&path);
};

PlaneHierarchy::PlaneHierarchy(int k) : cells(k * k), distances(k * k * k * k), k(k)
{
    Gcells.clear();
    Gcells.resize(n);
    double minX = min_element(input.begin(), input.end(), [](const Point &lhs, const Point &rhs) {
        return lhs.x() < rhs.x();
    })->x();
    double minY = min_element(input.begin(), input.end(), [](const Point &lhs, const Point &rhs) {
        return lhs.y() < rhs.y();
    })->y();
    double maxX = max_element(input.begin(), input.end(), [](const Point &lhs, const Point &rhs) {
        return lhs.x() < rhs.x();
    })->x();
    double maxY = max_element(input.begin(), input.end(), [](const Point &lhs, const Point &rhs) {
        return lhs.y() < rhs.y();
    })->y();
    double width = (maxX - minX) / k;
    double height = (maxY - minY) / k;
    pointToCell.reserve(input.size());
    for (int i = 0; i < input.size(); ++i) {
        int x = static_cast<int>((input[i].x() - minX) / width);
        int y = static_cast<int>((input[i].y() - minY) / height);
        getCellChecked(x, y).addPoint(i);
        pointToCell[i] = fixCellAddress(x, y);
    }
    for (auto &c : cells) {
        c.construct();
    }
}

metaCoords_t PlaneHierarchy::fixCellAddress(int x, int y) const
{
    if (x < 0) {
        x = 0;
    }
    if (y < 0) {
        y = 0;
    }
    if (x >= k) {
        assert(x == k);
        x -= 1;
    }
    if (y >= k) {
        assert(y == k);
        y -= 1;
    }
    assert(x * k + y < k * k);
    return {x, y};
}

void PlaneHierarchy::PlaneCell::chooseRepresentantPoint()
{
    // na razie środek ciężkości
    auto n = points.size();
    if (n == 0) {
        return; // reprezentant pozostaje niezainicjalizowany!
    }
    double x = 0, y = 0;
    for (auto p : points) {
        x += input[p].x();
        y += input[p].y();
    }
    representant = {x / n, y / n};
}

void PlaneHierarchy::PlaneCell::computeCandidates()
{
    const int nbNeighbors = 10;
    Delaunay D;
    vector<pair<Point, int>> delonePoints;
    for (int i : points) {
        delonePoints.push_back(make_pair(input[i], i));
    }
    D.insert(delonePoints.begin(), delonePoints.end());

    // otoczka wypukła
    if (points.size() < 2) {
        convexHull = points;
    } else {
        for (auto v : CGAL::Container_from_circulator<Delaunay::Vertex_circulator>(
                D.incident_vertices(D.infinite_vertex()))) {
            convexHull.push_back(v.info());
        }
    }

    // graf kandydatów
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
        assert(near.size() >= min<int>(nbNeighbors, points.size() - 1));
        for (auto &v : near) {
            if ((!D.is_infinite(v)) && (v != i->handle())) {
                neighbors.push_back(v->info());
            }
        }
        assert(neighbors.size() >= min<int>(nbNeighbors, points.size() - 1));
        Gproto[i->info()].insert(neighbors.begin(), neighbors.end());
        for (auto &v:neighbors) {
            Gproto[v].insert(i->info());
        }
    }
    for (int i : points) {
#ifdef DEBUG
        for (auto &v:Gproto[i]) {
            assert(Gproto[v].find(i) != Gproto[v].end());
        }
#endif
        Gcells[i].assign(Gproto[i].begin(), Gproto[i].end());
        assert(Gcells[i].size() >= min<int>(nbNeighbors, points.size() - 1));
    }
}

int PlaneHierarchy::euclid(metaCoords_t A, metaCoords_t B)
{
    assert(!getCell(A).empty());
    assert(!getCell(B).empty());
    if (A == B) {
        return 0; // nie modyfikuje struktury - nie powinna być używana w ten sposób
    }
    int distOffset = encodeMeta(A, B);
    if (distances[distOffset].distance == -1) {
#if 0   // CGAL oblicza coś nieco innego
        // oblicza odległość w oczekiwanym czasie liniowym za pomocą CGAL (nie potrzeba otoczki wypukłej)
        typedef CGAL::Polytope_distance_d_traits_2<K> Traits;
        typedef CGAL::Polytope_distance_d<Traits> Distance;
        auto &pointsA = getCell(A).getPoints();
        auto &pointsB = getCell(B).getPoints();
        Distance dist(pointsA.begin(), pointsA.end(), pointsB.begin(), pointsB.end());
        auto distSquared = dist.squared_distance();
        assert(distSquared >= 0);
        assert(distSquared != numeric_limits<decltype(distSquared)>::infinity());
        distances[distOffset].distance = static_cast<int>(sqrt(distSquared) + .5);
        distances[distOffset].from = dist.realizing_point_p();
        distances[distOffset].to = dist.realizing_point_q();
        auto distOffset2 = encodeMeta(B, A);
        distances[distOffset2].distance = static_cast<int>(sqrt(distSquared) + .5);
        distances[distOffset2].from = dist.realizing_point_q();
        distances[distOffset2].to = dist.realizing_point_p();
#ifdef DEBUG
        bool found = false;
        for (auto p : pointsA) {
            if (p == dist.realizing_point_p()) {
                found = true;
                break;
            }
        }
        assert(found);
        found = false;
        for (auto q : pointsB) {
            if (q == dist.realizing_point_q()) {
                found = true;
                break;
            }
        }
        assert(found);
#endif // DEBUG
#endif // 0
#if 0 // kolejna badziewna heureza
        // oblicza odległość między otoczkami wypukłymi heurystycznie (błędnie)
        // osobiśnie nie podoba mi się ten algorytm
        vector<int> hullA, hullB;
        const auto &pointsA = getCell(A).getPoints(), &pointsB = getCell(B).getPoints();
        {
            unordered_map<Point, int> pointToIdx;
            for (int i = 0; i < pointsA.size(); ++i) {
                pointToIdx[pointsA[i]] = i;
            }
            for (int i = 0; i < pointsB.size(); ++i) {
                pointToIdx[pointsB[i]] = i;
            }
            vector<Point> convexHullA, convexHullB;
            CGAL::convex_hull_2(pointsA.begin(), pointsA.end(), back_inserter(convexHullA));
            CGAL::convex_hull_2(pointsB.begin(), pointsB.end(), back_inserter(convexHullB));
            transform(convexHullA.begin(), convexHullA.end(), back_inserter(hullA),
                      [&pointToIdx](Point p) { return pointToIdx[p]; });
            transform(convexHullB.begin(), convexHullB.end(), back_inserter(hullB),
                      [&pointToIdx](Point p) { return pointToIdx[p]; });
        }
        using ::euclid;
        int aPtr = 0, bPtr = 0;
        int dist = euclid(pointsA[hullA[aPtr]], pointsB[hullB[bPtr]]);
        int aIncrement = 1; // w którą stronę iterować A
        if (pointsA.size() > 1 && (euclid(pointsA[hullA.back()], pointsB[hullB[bPtr]]) < dist)) {
            aIncrement = -1;
        }
        int bIncrement = 1; // w którą stronę iterować B
        if (pointsB.size() > 1 && (euclid(pointsA[hullA[aPtr]], pointsB[hullB.back()]) < dist)) {
            bIncrement = -1;
        } // mogą się źle poskładać ...
        for (; ;) {
            // przesuń A
            bool improved = false;
            while (euclid(pointsA[hullA[(aPtr + aIncrement + hullA.size()) % hullA.size()]], pointsB[hullB[bPtr]]) <
                   dist) {
                aPtr = (aPtr + aIncrement + hullA.size()) % hullA.size();
                dist = euclid(pointsA[hullA[aPtr]], pointsB[hullB[bPtr]]);
                improved = true;
            }
            if (!improved) {
                break;
            }
            // przesuń B
            improved = false;
            while (euclid(pointsA[hullA[aPtr]], pointsB[hullB[(bPtr + bIncrement + hullB.size()) % hullB.size()]]) <
                   dist) {
                bPtr = (bPtr + bIncrement + hullB.size()) % hullB.size();
                dist = euclid(pointsA[hullA[aPtr]], pointsB[hullB[bPtr]]);
                improved = true;
            }
            if (!improved) {
                break;
            }
        }
        distances[distOffset].distance = dist;
        distances[distOffset].from = hullA[aPtr];
        distances[distOffset].to = hullB[bPtr];
        auto distOffset2 = encodeMeta(B, A);
        distances[distOffset2].distance = dist;
        distances[distOffset2].to = hullA[aPtr];
        distances[distOffset2].from = hullB[bPtr];
#endif // 0
        // Oblicza graf delone obydwu zbioru punktów i wybiera najkrótszą krawędź o końcach z różnych zbiorów
        // to jest rozwiązanie dokładne
        //const auto &pointsA = getCell(A).getPoints(), &pointsB = getCell(B).getPoints();
        // ^^^^^ dobre, ale wolne

        const auto &pointsA = getCell(A).getConvexHull(), &pointsB = getCell(B).getConvexHull();
        // więc ograniczamy się tylko do punktów z otoczek
        Delaunay D;
        vector<pair<Point, int>> delonePoints;
        unordered_map<int, char> color;
        for (int i = 0; i < pointsA.size(); ++i) {
            delonePoints.push_back(make_pair(input[pointsA[i]], pointsA[i]));
            color[pointsA[i]] = 'A';
        }
        for (int i = 0; i < pointsB.size(); ++i) {
            delonePoints.push_back(make_pair(input[pointsB[i]], pointsB[i]));
            color[pointsB[i]] = 'B';
        }
        D.insert(delonePoints.begin(), delonePoints.end());
        int lowestDist = numeric_limits<int>::max();
        int pointX, pointY; // na razie nie wiadomo który to A, B
        for (auto i = D.finite_edges_begin(), e = D.finite_edges_end(); i != e; ++i) {
            auto &face = i->first;
            auto param = i->second;
            int v1 = face->vertex(face->cw(param))->info();
            int v2 = face->vertex(face->ccw(param))->info();
            if (color[v1] == color[v2]) {
                continue;
            }
            using ::euclid;
            if (euclid(v1, v2) < lowestDist) {
                lowestDist = euclid(v1, v2);
                pointX = v1;
                pointY = v2;
            }
        }
        assert(lowestDist != numeric_limits<int>::max());
        assert(color[pointX] != color[pointY]);
        if (color[pointX] == 'B') {
            using std::swap;
            swap(pointX, pointY);
        }
        assert(color[pointX] == 'A');
        assert(color[pointY] == 'B');
        distances[distOffset].distance = lowestDist;
        distances[distOffset].from = pointX;
        distances[distOffset].to = pointY;
        auto distOffset2 = encodeMeta(B, A);
        distances[distOffset2].distance = lowestDist;
        distances[distOffset2].to = pointX;
        distances[distOffset2].from = pointY;

    }
    return distances[distOffset].distance;
}

vector<metaCoords_t> PlaneHierarchy::chooseMetaCycle()
{
    list <metaCoords_t> result;
    {
        unordered_map<Point, pair<metaCoord_t, metaCoord_t>> pointToMetaCoord;
        vector<Point> pointsForHull;
        for (int x = 0; x < k; ++x) {
            for (int y = 0; y < k; ++y) {
                auto &c = getCell(x, y);
                if (c.empty()) {
                    continue;
                }
                Point p = c.getRepresentant();
                pointsForHull.push_back(p);
                pointToMetaCoord[p] = {x, y};
            }
        }
        vector<Point> convexHullOrder;
        CGAL::convex_hull_2(pointsForHull.begin(), pointsForHull.end(), back_inserter(convexHullOrder));
        transform(convexHullOrder.begin(), convexHullOrder.end(), back_inserter(result),
                  [&pointToMetaCoord](Point p) { return pointToMetaCoord[p]; });
    }
    vector<bool> metaVertexInResult(k * k);
    list <metaCoords_t> remainingVertices;
    vector<int> distanceToResult(k * k, numeric_limits<int>::max());
    for (auto p : result) {
        metaVertexInResult[encode(p.first, p.second)] = true;
    }
    for (int x = 0; x < k; ++x) {
        for (int y = 0; y < k; ++y) {
            if (metaVertexInResult[encode(x, y)] || getCell(x, y).empty()) {
                continue;
            }
            remainingVertices.push_back({x, y});
        }
    }
    for (auto r : remainingVertices) {
        for (auto p : result) {
            distanceToResult[encode(r.first, r.second)] = min(distanceToResult[encode(r.first, r.second)],
                                                              euclid(r, p));
        }
    }
    while (!remainingVertices.empty()) {
        // wybierz najdalszy punkt
        int bestDistnace = -1;
        pair<metaCoord_t, metaCoord_t> P;
        auto selectedVertex = remainingVertices.end();
        for (auto candidate = remainingVertices.begin(); candidate != remainingVertices.end(); ++candidate) {
            int x = candidate->first;
            int y = candidate->second;
            assert(!metaVertexInResult[encode(x, y)] && !getCell(x, y).empty());
            int dist = distanceToResult[encode(x, y)];
            if (dist > bestDistnace) {
                bestDistnace = dist;
                P = {x, y};
                selectedVertex = candidate;
            }
        }
        assert (bestDistnace != -1);
        assert(selectedVertex != remainingVertices.end());
        // wstaw wybrany punkt P
        auto position = result.begin();
        int price = euclid(result.back(), P) + euclid(P, result.front()) - euclid(result.back(), result.front());
        for (auto j = result.begin(), i = j++; j != result.end(); ++j, ++i) {
            int newPrice = euclid(*i, P) + euclid(P, *j) - euclid(*i, *j);
            if (newPrice < price) {
                price = newPrice;
                position = j;
            }
        }
        result.insert(position, P);
        metaVertexInResult[encode(P)] = true;
        remainingVertices.erase(selectedVertex);
        // aktualizuj odległości
        for (auto r :remainingVertices) {
            int x = r.first;
            int y = r.second;
            assert(!metaVertexInResult[encode(x, y)] && !getCell(x, y).empty());
            distanceToResult[encode(x, y)] = min(distanceToResult[encode(x, y)], euclid({x, y}, P));
        }
    }
    return optimized(move(result));
}

vector<int> PlaneHierarchy::choosePathForChunk(metaCoords_t before, metaCoords_t chunk, metaCoords_t after)
{
    assert(before != chunk);
    assert(after != chunk);
    // NOTE before może być == after
    euclid(chunk, before); // potrzebny efekt uboczny - wskazanie wierzchołków "przejściowych"
    euclid(chunk, after);
    assert(distances[encodeMeta(chunk, before)].distance != -1);
    assert(distances[encodeMeta(chunk, after)].distance != -1);
    int begin = distances[encodeMeta(chunk, before)].from;
    int end = distances[encodeMeta(chunk, after)].from;
    const vector<int> &pointsIndices = getCell(chunk).getPoints();
    list<int> result;
    list<int> remainingVertices;
    vector<int> distanceToResult(n, numeric_limits<int>::max());
    using ::euclid;
    {
        // kawałek otoczki
        const vector<int> &hull = getCell(chunk).getConvexHull();
        // wybór lepszej połowy
        if (__builtin_expect(begin == end, false)) {
            // głupi przypadek brzegowy - ścieżka chciałaby zaczynać się i kończyć w tym samym wierzchołku
            auto newBegin = find(hull.begin(), hull.end(), begin);
            if (__builtin_expect(newBegin != hull.end(), true)) {
                copy(newBegin, hull.end(), back_inserter(result));
                copy(hull.begin(), newBegin, back_inserter(result));
            } else {
                // punkt realizujący początek i koniec nie jest na otoczce
                result = {begin};
            }
        } else {
            // "normalny" przypadek
            auto beginPosition = find(hull.begin(), hull.end(), begin);
            auto endPosition = find(hull.begin(), hull.end(), end);
            if (__builtin_expect(beginPosition != hull.end() && endPosition != hull.end(), true)) {
                // C++11 distance na RandomAccessIterator jest legalne bez względu na kolejność
                auto internalLength = abs(distance(beginPosition, endPosition)) - 1;
                auto externalLength = hull.size() - internalLength;
                if (internalLength >= externalLength) {
                    if (beginPosition < endPosition) {
                        copy(beginPosition, endPosition + 1, back_inserter(result));
                    } else {
                        reverse_copy(endPosition, beginPosition + 1, back_inserter(result));
                    }
                } else {
                    if (beginPosition < endPosition) {
                        reverse_copy(hull.begin(), beginPosition + 1, back_inserter(result));
                        reverse_copy(endPosition, hull.end(), back_inserter(result));
                    } else {
                        copy(beginPosition, hull.end(), back_inserter(result));
                        copy(hull.begin(), endPosition + 1, back_inserter(result));
                    }
                }
            } else {
                // punkty realizujące początek i koniec ścieżki nie są na otoczce
                result = {begin, end};
            }
        }
        vector<bool> vertexInResult(n);
        for (int index : result) {
            assert(index < n);
            vertexInResult[index] = true;
        }
        for (int p : pointsIndices) {
            if (!vertexInResult[p]) {
                remainingVertices.push_back(p);
            }
        }
        for (auto r : remainingVertices) {
            for (auto p : result) {
                distanceToResult[r] = min(distanceToResult[r], euclid(r, p));
            }
        }
    }
    assert(remainingVertices.size() == pointsIndices.size() - result.size());
    while (result.size() != pointsIndices.size()) {
        assert(!remainingVertices.empty());
        // wybierz najdalszy od result
        auto nextVertexIdx = remainingVertices.begin();
        int maxDistFromResultSet = -1;
        for (auto candidate = remainingVertices.begin(), e = remainingVertices.end(); candidate != e; ++candidate) {
            int minDistToResultSet = distanceToResult[*candidate];
            if (minDistToResultSet > maxDistFromResultSet) {
                maxDistFromResultSet = minDistToResultSet;
                nextVertexIdx = candidate;
            }
        }
        int vertex = *nextVertexIdx;
        remainingVertices.erase(nextVertexIdx);
        // wstaw vertex w najlepsze miejsce
        auto position = result.end();
        int price = numeric_limits<int>::max();
        for (auto j = result.begin(), i = j++; j != result.end(); ++j, ++i) {
            int newPrice = euclid(*i, vertex) + euclid(vertex, *j) - euclid(*i, *j);
            if (newPrice < price) {
                price = newPrice;
                position = j;
            }
        }
        result.insert(position, vertex);
        // aktualizuj odległości
        for (auto r :remainingVertices) {
            distanceToResult[r] = min(distanceToResult[r], euclid(r, vertex));
        }
    }
    assert(remainingVertices.empty());
    return optimized(chunk, move(result));
}

struct ChoiceBaseMetaGraph
{
    int improvement;
    int realImprovement;
    metaCoords_t vertex;
    metaCoords_t secondVertex;

    ChoiceBaseMetaGraph() : improvement(numeric_limits<int>::min())
    { }

    ChoiceBaseMetaGraph(metaCoords_t vertex, metaCoords_t secondVertex) : vertex(vertex), secondVertex(secondVertex)
    { }

    bool empty() const
    {
        return improvement == numeric_limits<int>::min();
    }

    virtual void execute(PlaneHierarchy &plane, SplayTree<uint16_t> &order) const = 0;

    //virtual void markUsedEdges(SplayTree &order, UsedEdgesSet &usedEdges) const = 0;
};

struct NodeInsertionChoiceMetaGraph : ChoiceBaseMetaGraph
{
    NodeInsertionChoiceMetaGraph() = default;

    NodeInsertionChoiceMetaGraph(PlaneHierarchy &plane, metaCoords_t vertex, metaCoords_t before, metaCoords_t after,
                                 metaCoords_t first, metaCoords_t last) : ChoiceBaseMetaGraph(vertex, last)
    {
        improvement = plane.euclid(before, vertex) + plane.euclid(vertex, after) - plane.euclid(before, after) -
                      plane.euclid(vertex, last);
        realImprovement = improvement + plane.euclid(first, last) - plane.euclid(first, vertex);
    }

    virtual void execute(PlaneHierarchy &plane, SplayTree<uint16_t> &order) const override
    {
        order.moveToEnd(plane.encode(vertex));
    }

    //virtual void markUsedEdges(SplayTree &order, UsedEdgesSet &usedEdges) const override;
};

struct TwoOptChoiceMetaGraph : ChoiceBaseMetaGraph
{
    TwoOptChoiceMetaGraph() = default;

    TwoOptChoiceMetaGraph(PlaneHierarchy &plane, metaCoords_t vertex, metaCoords_t before, metaCoords_t after,
                          metaCoords_t first, metaCoords_t last) : ChoiceBaseMetaGraph(vertex, last)
    {
        improvement = plane.euclid(vertex, after) - plane.euclid(vertex, last);
        realImprovement = improvement + plane.euclid(first, last) - plane.euclid(first, after);
    }

    virtual void execute(PlaneHierarchy &plane, SplayTree<uint16_t> &order) const override
    {
        order.reverseAfter(plane.encode(vertex));
    }

    //virtual void markUsedEdges(SplayTree &order, UsedEdgesSet &usedEdges) const override;
};

vector<metaCoords_t> PlaneHierarchy::optimized(list <metaCoords_t> &&path)
{
    assert(numeric_limits<uint16_t>::max() > k * k);
    vector<uint16_t> pathVector;
    pathVector.reserve(path.size());
    for (auto p : path) {
        assert(encode(p) <= numeric_limits<uint16_t>::max());
        pathVector.push_back(encode(p));
    }
    SplayTree<uint16_t> currentPath(pathVector.begin(), pathVector.end());
    for (bool improved = true; improved;) {
        improved = false;
        for (auto active : path) {
            currentPath.cyclicRotateToEnd(encode(active));
            for (; ;) {
                NodeInsertionChoiceMetaGraph bestNodeInsertionChoice;
                TwoOptChoiceMetaGraph bestTwoOptChoice;
                auto first = decode(currentPath.first());
                auto last = decode(currentPath.last());
                for (auto a : path) {
                    if (last == a) {
                        continue;
                    }
                    // splay może być mały (2... (k))
                    auto before = currentPath.before(encode(a));
                    auto after = currentPath.after(encode(a));
                    assert(after != SplayTree<uint16_t>::null);
                    // node insertion
                    if ((before != SplayTree<uint16_t>::null) /*&& (!usedEdges.hasEdge(a, last))*/) {
                        NodeInsertionChoiceMetaGraph choice(*this, a, decode(before), decode(after), first, last);
                        if (bestNodeInsertionChoice.empty() ||
                            bestNodeInsertionChoice.improvement < choice.improvement) {
                            bestNodeInsertionChoice = choice;
                        }
                    }
                    // 2-opt
                    if (/*!usedEdges.hasEdge(a, last)*/ true) {
                        TwoOptChoiceMetaGraph choice(*this, a, decode(before), decode(after), first, last);
                        if (bestTwoOptChoice.empty() || bestTwoOptChoice.improvement < choice.improvement) {
                            bestTwoOptChoice = choice;
                        }
                    }
                }
                unique_ptr<ChoiceBaseMetaGraph> bestDecision;
                if (bestNodeInsertionChoice.empty() && bestTwoOptChoice.empty()) {
                    break; // kolejne iteracje i tak nic nie zrobią
                } else if (!bestNodeInsertionChoice.empty() && !bestTwoOptChoice.empty()) {
                    if (bestNodeInsertionChoice.improvement >= bestTwoOptChoice.improvement) {
                        bestDecision.reset(new NodeInsertionChoiceMetaGraph(bestNodeInsertionChoice));
                    } else {
                        bestDecision.reset(new TwoOptChoiceMetaGraph(bestTwoOptChoice));
                    }
                } else if (!bestNodeInsertionChoice.empty()) {
                    bestDecision.reset(new NodeInsertionChoiceMetaGraph(bestNodeInsertionChoice));
                } else {
                    assert(!bestTwoOptChoice.empty());
                    bestDecision.reset(new TwoOptChoiceMetaGraph(bestTwoOptChoice));
                }
                if (bestDecision->realImprovement > 0) {
                    bestDecision->execute(*this, currentPath);
                    improved = true;
                } else {
                    break;
                }
                //bestDecision->markUsedEdges(currentPath, usedEdges);
            }
        }
    }
    pathVector = currentPath.dumpOrderly();
    vector<metaCoords_t> result;
    result.reserve(pathVector.size());
    transform(pathVector.begin(), pathVector.end(), back_inserter(result), [this](uint16_t ep) { return decode(ep); });
    return result;
}

struct ChoiceBase
{
    int improvement;
    int realImprovement;
    int vertex;
    int secondVertex;

    ChoiceBase() : improvement(numeric_limits<int>::min())
    { }

    ChoiceBase(int vertex, int secondVertex) : vertex(vertex), secondVertex(secondVertex)
    { }

    bool empty() const
    {
        return improvement == numeric_limits<int>::min();
    }

    virtual void execute(SplayTree<int> &order) const = 0;

    //virtual void markUsedEdges(SplayTree &order, UsedEdgesSet &usedEdges) const = 0;
};

struct NodeInsertionChoice : ChoiceBase
{
    NodeInsertionChoice() = default;

    NodeInsertionChoice(int vertex, int before, int after, int first, int last) : ChoiceBase(vertex, last)
    {
        improvement = euclid(before, vertex) + euclid(vertex, after) - euclid(before, after) - euclid(vertex, last);
        realImprovement = improvement + euclid(first, last) - euclid(first, vertex);
    }

    virtual void execute(SplayTree<int> &order) const override
    {
        order.moveToEnd(vertex);
    }

    //virtual void markUsedEdges(SplayTree &order, UsedEdgesSet &usedEdges) const override;
};

struct TwoOptChoice : ChoiceBase
{
    TwoOptChoice() = default;

    TwoOptChoice(int vertex, int before, int after, int first, int last) : ChoiceBase(vertex, last)
    {
        improvement = euclid(vertex, after) - euclid(vertex, last);
        realImprovement = improvement + euclid(first, last) - euclid(first, after);
    }

    virtual void execute(SplayTree<int> &order) const override
    {
        order.reverseAfter(vertex);
    }

    //virtual void markUsedEdges(SplayTree &order, UsedEdgesSet &usedEdges) const override;
};

vector<int> PlaneHierarchy::optimized(metaCoords_t chunk, list<int> &&path)
{
    vector<int> pathVector(path.begin(), path.end());
    list<int>().swap(path);
    SplayTree<int> currentPath(pathVector.begin(), pathVector.end());
    vector<int>().swap(pathVector);
    for (bool improved = true; improved;) {
        improved = false;
        for (int active: path) {
            currentPath.cyclicRotateToEnd(active);
            //for (; ;) {
            NodeInsertionChoice bestNodeInsertionChoice;
            TwoOptChoice bestTwoOptChoice;
            auto first = currentPath.first();
            auto last = currentPath.last();
            assert(pointToCell[last] == chunk);
            for (auto a : Gcells[last]) {
                if (pointToCell[a] != chunk) {
                    continue;
                }
                assert(last != a);
                auto before = currentPath.before(a);
                auto after = currentPath.after(a);
                assert(after != SplayTree<int>::null);
                // node insertion
                if ((before != SplayTree<int>::null) /*&& (!usedEdges.hasEdge(a, last))*/) {
                    NodeInsertionChoice choice(a, before, after, first, last);
                    if (bestNodeInsertionChoice.empty() || bestNodeInsertionChoice.improvement < choice.improvement) {
                        bestNodeInsertionChoice = choice;
                    }
                }
                // 2-opt
                if (/*!usedEdges.hasEdge(a, last)*/ true) {
                    TwoOptChoice choice(a, before, after, first, last);
                    if (bestTwoOptChoice.empty() || bestTwoOptChoice.improvement < choice.improvement) {
                        bestTwoOptChoice = choice;
                    }
                }
            }
            unique_ptr<ChoiceBase> bestDecision;
            if (bestNodeInsertionChoice.empty() && bestTwoOptChoice.empty()) {
                break; // kolejne iteracje i tak nic nie zrobią
            } else if (!bestNodeInsertionChoice.empty() && !bestTwoOptChoice.empty()) {
                if (bestNodeInsertionChoice.improvement >= bestTwoOptChoice.improvement) {
                    bestDecision.reset(new NodeInsertionChoice(bestNodeInsertionChoice));
                } else {
                    bestDecision.reset(new TwoOptChoice(bestTwoOptChoice));
                }
            } else if (!bestNodeInsertionChoice.empty()) {
                bestDecision.reset(new NodeInsertionChoice(bestNodeInsertionChoice));
            } else {
                assert(!bestTwoOptChoice.empty());
                bestDecision.reset(new TwoOptChoice(bestTwoOptChoice));
            }
            if (bestDecision->realImprovement > 0) {
                bestDecision->execute(currentPath);
                improved = true;
            } else {
                //break;
            }
            //bestDecision->markUsedEdges(currentPath, usedEdges);
            //}
        }
    }
    return currentPath.dumpOrderly();
}

static vector<int> optimized(vector<int> &&path)
{
    SplayTree<int> currentPath(path.begin(), path.end());
    vector<int>().swap(path);
    bool improved = true;
    for (int i = 0; (i < 5) && improved; ++i) {
        improved = false;
        for (int activeNode = 0; activeNode < n; ++activeNode) {
            currentPath.cyclicRotateToEnd(activeNode);
            for (; ;) {
                NodeInsertionChoice bestNodeInsertionChoice;
                TwoOptChoice bestTwoOptChoice;
                auto first = currentPath.first();
                auto last = currentPath.last();
                for (auto a : G[last]) {
                    assert(last != a);
                    auto before = currentPath.before(a);
                    auto after = currentPath.after(a);
                    assert(after != SplayTree<int>::null);
                    // node insertion
                    if ((before != SplayTree<int>::null) /*&& (!usedEdges.hasEdge(a, last))*/) {
                        NodeInsertionChoice choice(a, before, after, first, last);
                        if (bestNodeInsertionChoice.empty() ||
                            bestNodeInsertionChoice.improvement < choice.improvement) {
                            bestNodeInsertionChoice = choice;
                        }
                    }
                    // 2-opt
                    if (/*!usedEdges.hasEdge(a, last)*/ true) {
                        TwoOptChoice choice(a, before, after, first, last);
                        if (bestTwoOptChoice.empty() || bestTwoOptChoice.improvement < choice.improvement) {
                            bestTwoOptChoice = choice;
                        }
                    }
                }
                unique_ptr<ChoiceBase> bestDecision;
                if (bestNodeInsertionChoice.empty() && bestTwoOptChoice.empty()) {
                    break; // kolejne iteracje i tak nic nie zrobią
                } else if (!bestNodeInsertionChoice.empty() && !bestTwoOptChoice.empty()) {
                    if (bestNodeInsertionChoice.improvement >= bestTwoOptChoice.improvement) {
                        bestDecision.reset(new NodeInsertionChoice(bestNodeInsertionChoice));
                    } else {
                        bestDecision.reset(new TwoOptChoice(bestTwoOptChoice));
                    }
                } else if (!bestNodeInsertionChoice.empty()) {
                    bestDecision.reset(new NodeInsertionChoice(bestNodeInsertionChoice));
                } else {
                    assert(!bestTwoOptChoice.empty());
                    bestDecision.reset(new TwoOptChoice(bestTwoOptChoice));
                }
                if (bestDecision->realImprovement > 0) {
                    bestDecision->execute(currentPath);
                    improved = true;
                } else {
                    break;
                }
                //bestDecision->markUsedEdges(currentPath, usedEdges);
            }
        }
    }
    return currentPath.dumpOrderly();
}

template<typename DContainer, typename SContainer>
void copy(DContainer &dest, const SContainer &source)
{
    copy(source.begin(), source.end(), back_inserter(dest));
};

int main()
{
    //close(0);
    //open("/home/local/AA/F/testy/55.in", O_RDONLY);
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
        int k = static_cast<int>(sqrt(sqrt(n)) + .5);
        if (k == 1) {
            k = 2; // patrz fixme poniżej
            // teraz powinny istnieć przynajmniej 2 meta wierzchołki (bo n>=2)
        }
        PlaneHierarchy plane(k);
        auto metaCycle = plane.chooseMetaCycle();
        assert(metaCycle.size() > 1);   // patrz fixme
        vector<int> result;
        result.reserve(n);
        copy(result, plane.choosePathForChunk(metaCycle.back(), metaCycle.front(), *++metaCycle.begin()));
        for (auto R = metaCycle.begin(), L = R++, C = R++, e = metaCycle.end(); R != e; ++L, ++C, ++R) {
            // fragment cyklu .. - L - C - R - ..
            // FIXME Jeżeli k==1 to potrzebujemy _cyklu_ a nie ścieżki w komórce - potrzebna jest inna implementacja
            copy(result, plane.choosePathForChunk(*L, *C, *R));
        }
        copy(result, plane.choosePathForChunk(*++metaCycle.rbegin(), metaCycle.back(), metaCycle.front()));

        result = optimized(move(result));

        for (int v : result) {
            cout << v << ' ';
        }
        cout << '\n' << getHamiltonianLength(result.begin(), result.end()) << '\n';
    }
}