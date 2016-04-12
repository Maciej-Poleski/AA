//Maciej Poleski
//#define DEBUG
#ifndef DEBUG
#define NDEBUG
#else
#define _GLIBCXX_CONCEPT_CHECKS
#define TEST_SPLAY
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

static double dist(int v, int w)
{
    double x = input[v].x() - input[w].x();
    double y = input[v].y() - input[w].y();
    return hypot(x, y);
}

//#if 0
static int euclid(int v, int w)
{
    return static_cast<int>(dist(v, w) + 0.5);
}
//#endif

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

static long getHamiltonianLength(const vector<int> &hamiltonian)
{
    long result = 0;
    for (unsigned i = 1; i < hamiltonian.size(); ++i) {
        result += euclid(hamiltonian[i - 1], hamiltonian[i]);
    }
    result += euclid(hamiltonian.back(), hamiltonian.front());
    return result;
}

// Reprezentuje ciąg składający się z liczb 0..(n-1)
class SplayTree
{
public:
    struct Node
    {
        uint16_t parent;
        uint16_t left, right;
        bool reversed;
    };

public:
    static constexpr uint16_t null = numeric_limits<uint16_t>::max();

    SplayTree(uint_fast16_t n); // Na początku ciąg 0..(n-1)

    uint_fast16_t before(uint_fast16_t vertex);

    uint_fast16_t after(uint_fast16_t vertex);

    vector<uint16_t> dumpOrderly() const;

    void moveToEnd(uint_fast16_t vertex);

    void reverseAfter(uint_fast16_t vertex);

private:
    vector<Node> chunk;
    uint_fast16_t root;

    void dispatchReversal(uint_fast16_t vertex);

    uint16_t &left(uint_fast16_t v)
    {
        assert(v != null);
        return chunk[v].left;
    }

    uint16_t &right(uint_fast16_t v)
    {
        assert(v != null);
        return chunk[v].right;
    }

    uint16_t &parent(uint_fast16_t v)
    {
        assert(v != null);
        return chunk[v].parent;
    }

    bool &reversed(uint_fast16_t v)
    {
        assert(v != null);
        return chunk[v].reversed;
    }

    bool isParent(uint_fast16_t p, uint_fast16_t chld)
    {
        if (p == null) {
            return (root == chld) && (parent(chld) == p);
        }
        return ((chld == null) || (parent(chld) == p)) && ((left(p) == chld) || (right(p) == chld));
    }

    void setLeftChild(uint16_t v, uint16_t child)
    {
        assert(v != null);
        left(v) = child;
        if (child != null) {
            parent(child) = v;
        }
        assert(isParent(v, child));
    }

    void setRightChild(uint16_t v, uint16_t child)
    {
        assert(v != null);
        right(v) = child;
        if (child != null) {
            parent(child) = v;
        }
        assert(isParent(v, child));
    }

    void substituteChild(uint16_t v, uint16_t oldChild, uint16_t newChild)
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

    void zig(uint_fast16_t x);

    void zigZig(uint_fast16_t x);

    void zigZag(uint_fast16_t x);

    void splay(uint_fast16_t vertex);
};

// Ustawia left, right, reversed. Nie ustawia parent
static uint16_t buildStructure(vector<SplayTree::Node> &chunk, uint_fast16_t begin, uint_fast16_t end)
{
    assert(begin <= end);
    assert(end != SplayTree::null);
    if (begin == end) {
        return SplayTree::null;
    } else if (begin + 1 == end) {
        chunk[begin].left = chunk[begin].right = SplayTree::null;
        chunk[begin].reversed = false;
        return begin;
    }
    uint16_t center = (begin + end) / 2;
    auto left = chunk[center].left = buildStructure(chunk, begin, center);
    auto right = chunk[center].right = buildStructure(chunk, center + 1, end);
    if (left != SplayTree::null) {
        chunk[left].parent = center;
    }
    if (right != SplayTree::null) {
        chunk[right].parent = center;
    }
    assert(chunk[center].left != center);
    assert(chunk[center].right != center);
    return center;
}

SplayTree::SplayTree(uint_fast16_t n) : chunk(n)
{
    root = buildStructure(chunk, 0, n);
    parent(root) = null;
#ifdef TEST_SPLAY
    for (int i = 0; i < n; ++i) {
        assert(isParent(parent(i), i));
        assert(isParent(i, left(i)));
        assert(isParent(i, right(i)));
    }
#endif
}

uint_fast16_t SplayTree::before(uint_fast16_t vertex)
{
    splay(vertex);
    assert(!reversed(vertex));
    if (left(vertex) == null) {
        return null;
    }
    auto i = left(vertex);
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

// co szkodziłoby zrobić before zakładając wstępnie że reversed?
uint_fast16_t SplayTree::after(uint_fast16_t vertex)
{
    splay(vertex);
    assert(!reversed(vertex));
    if (right(vertex) == null) {
        return null;
    }
    auto i = right(vertex);
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

static void dumpSplayChunk(const vector<SplayTree::Node> &chunk, uint_fast16_t v, bool reverse, vector<uint16_t> &order)
{
    if (v == SplayTree::null) {
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

vector<uint16_t> SplayTree::dumpOrderly() const
{
    vector<uint16_t> result;
    dumpSplayChunk(chunk, root, false, result);
    return result;
}

void SplayTree::moveToEnd(uint_fast16_t vertex)
{
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
    if (right(vertex)) {
        reversed(right(vertex)) = !reversed(right(vertex));
    }
}

void SplayTree::reverseAfter(uint_fast16_t vertex)
{
    splay(vertex);
    assert(!reversed(vertex));
    auto r = right(vertex);
    if (r != null) {
        reversed(r) = !reversed(r);
    }
}

void SplayTree::dispatchReversal(uint_fast16_t vertex)
{
    if (reversed(vertex)) {
        reversed(vertex) = false;
        swap(left(vertex), right(vertex));
        if (left(vertex) != null) {
            reversed(left(vertex)) = !reversed(left(vertex));
        }
        if (right(vertex) != null) {
            reversed(right(vertex)) = !reversed(right(vertex));
        }
    }
}

void SplayTree::zig(uint_fast16_t x)
{
    assert(x < chunk.size());
    uint16_t p = parent(x);
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

void SplayTree::zigZig(uint_fast16_t x)
{
    assert(x < chunk.size());
    uint16_t p = parent(x);
    assert(p < chunk.size());
    uint16_t g = parent(p);
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

void SplayTree::zigZag(uint_fast16_t x)
{
    assert(x < chunk.size());
    uint16_t p = parent(x);
    assert(p < chunk.size());
    uint16_t g = parent(p);
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

void SplayTree::splay(uint_fast16_t vertex)
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
#ifdef TEST_SPLAY
    auto newOrder = dumpOrderly();
    assert(oldOrder == newOrder);
#endif
}

int main()
{
    close(0);
    open("/home/local/AA/D/testy/t00.in", O_RDONLY);
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
        assert(G.size() == n);
        const int16_t size = 10000;
        SplayTree tree(size);
        vector<int16_t> referenceOrder(size);
        uniform_int_distribution<uint16_t> dist(0, size - 1);
        auto ord = tree.dumpOrderly();
        assert(ord.size() == size);
        for (uint16_t i = 0; i < size; ++i) {
            referenceOrder[i] = i;
            assert(ord[i] == i);
        }
        for (int i = 0; i < 1000; ++i) {
            auto position = dist(randomEngine);
            auto it = find(referenceOrder.begin(), referenceOrder.end(), position);
            reverse(it + 1, referenceOrder.end());
            tree.reverseAfter(position);
            ord = tree.dumpOrderly();
            assert(ord.size() == size);
            for (uint16_t i = 0; i < size; ++i) {
                assert(ord[i] == referenceOrder[i]);
            }
            assert((tree.before(position) == SplayTree::null) || (tree.before(position) == *(it - 1)));
            assert((tree.after(position) == SplayTree::null) || (tree.after(position) == *(it + 1)));

        }
    }
    return 0;
}