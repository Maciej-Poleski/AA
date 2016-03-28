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
    const int nbNeighbors = 40;
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

static int saving(int centralVertex, int a, int b)
{
    return -(euclid(a, b) - euclid(a, centralVertex) - euclid(b, centralVertex));
}

class Node
{
public:
    virtual bool isLeaf() const = 0;

    virtual void reverse() = 0;

    virtual void dumpOrderly(vector<int> &order, bool reversed = false) const = 0;
};

struct Leaf : Node
{
    int vertex;

    Leaf(int vertex) : vertex(vertex)
    { }

    virtual bool isLeaf() const override
    {
        return true;
    }

    virtual void reverse() override
    {
        // do nothing
    }

    virtual void dumpOrderly(vector<int> &order, bool reversed) const override
    {
        (void) reversed;
        order.push_back(vertex);
    }
};

struct InternalNode : Node
{
    shared_ptr<Node> left, right;
    bool reversed = false;

    InternalNode(const shared_ptr<Node> &left, const shared_ptr<Node> &right);

    virtual bool isLeaf() const override
    {
        return false;
    }

    virtual void reverse() override
    {
        assert(reversed == false);
        reversed = true;
    }

    virtual void dumpOrderly(vector<int> &order, bool reversed) const override;
};

InternalNode::InternalNode(const shared_ptr<Node> &left, const shared_ptr<Node> &right) : left(left), right(right)
{
}

void InternalNode::dumpOrderly(vector<int> &order, bool reversed) const
{
    bool rev = reversed != this->reversed;
    auto l = left, r = right;
    if (rev) {
        swap(l, r);
    }
    l->dumpOrderly(order, rev);
    r->dumpOrderly(order, rev);
}

enum class Side : bool
{
    Left = false, Right = true,
};

int main()
{
    //close(0);
    //open("/home/local/AA/C/testy/t00.in", O_RDONLY);
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
        uniform_int_distribution<int> startVertex(0, n - 1);
        vector<int> bestResult;
        long resultLength = numeric_limits<long>::max();
        for (int rootRepeat = 0; rootRepeat < 7; ++rootRepeat) {
            vector<pair<int, pair<int, int >>> edges;
            int centralVertex = startVertex(randomEngine);
            for (int i = 0; i < n; ++i) {
                if (i == centralVertex) {
                    continue;
                }
                for (int v:G[i]) {
                    if (v == centralVertex) {
                        continue;
                    }
                    int a = i;
                    int b = v;
                    assert(a != b);
                    if (a > b) {
                        swap(a, b);
                    }
                    edges.push_back({saving(centralVertex, a, b), {a, b}});
                }
            }
            sort(edges.begin(), edges.end(),
                 [](const pair<int, pair<int, int>> &lhs, const pair<int, pair<int, int>> &rhs) {
                     return lhs.first > rhs.first;
                 });
            edges.erase(unique(edges.begin(), edges.end()), edges.end());
            unordered_set<int> cornerVertices;
            vector<pair<shared_ptr<Node>, Side >> vertexToTree(n);
            vector<int> currentDegree(n);
            vector<int> otherSide(n);
            for (int i = 0; i < n; ++i) {
                if (i == centralVertex) {
                    continue;
                }
                cornerVertices.insert(i);
                shared_ptr<Leaf> newLeaf = make_shared<Leaf>(i);
                vertexToTree[i] = {newLeaf, Side::Left};
                currentDegree[i] = G[i].size();
                otherSide[i] = i; // początkowo listki są jednoelementowe
            }
            for (const auto edge : edges) {
                int a = edge.second.first;
                int b = edge.second.second;
                assert(a < b);
                assert(a != centralVertex);
                assert(b != centralVertex);
                currentDegree[a] -= 1;
                currentDegree[b] -= 1;
                if (cornerVertices.count(a) > cornerVertices.count(b)) {
                    swap(a, b);
                }
                // cornerVertices.count(a) <= cornerVertices.count(b)
                if (cornerVertices.count(b) == 0) {
                    continue;
                } // cornerVertices.count(b) == 1
                if (cornerVertices.count(a) == 0 && currentDegree[b] == 0) {
                    // b jest na początku/końcu, a nie jest, ale b widzimy po raz ostatni - poszukaj jakiegoś innego a
                    // krawędź {a,b} jest odrzucana ale
                    // jeżeli znajdziemy nowe a na początku/końcu, nie będzie krawędzi {a,b} w grafie kandydatów
                    // nie spadnie stopień żadnych innych wierzchołków
                    int candidate;
                    int saving = -1; // nierównośc trójkąta gwarantuje możliwość uzyskania wyniku co najmniej 0
                    for (int v : cornerVertices) {
                        if (v == b || otherSide[v] == b) {
                            continue; // szukamy istotnie innego wierzchołka
                        }
                        if (::saving(centralVertex, v, b) > saving) {
                            saving = ::saving(centralVertex, v, b);
                            candidate = v;
                        }
                    }
                    if (saving == -1) {
                        continue;
                        // w zasadzie już skończyliśmy (został dokładnie 1 listek)
                    }
                    a = candidate;
                    assert(cornerVertices.count(a) == 1); // nadmiarowe, ale niech będzie
                }
                if (cornerVertices.count(a) == 1) {
                    if (otherSide[a] == b) {
                        assert(otherSide[b] == a);
                        continue; // tak nie można łączyć
                    }
                    // można połączyć
                    auto infoA = vertexToTree[a];
                    auto infoB = vertexToTree[b];
                    const bool aIsLeaf = infoA.first->isLeaf();
                    const bool bIsLeaf = infoB.first->isLeaf();
                    if (infoA.second == Side::Left) {
                        infoA.first->reverse();
                    }
                    if (infoB.second == Side::Right) {
                        infoB.first->reverse();
                    }
                    shared_ptr<InternalNode> newNode = make_shared<InternalNode>(infoA.first, infoB.first);
                    // aL---a...b---bR  -->  aL---a-b---bR
                    const int aL = otherSide[a];
                    const int bR = otherSide[b];
                    otherSide[aL] = bR;
                    otherSide[bR] = aL;
                    // otherSide[a], otherSide[b] - już nie ważne
                    // najpierw kasuj dojścia do wewnętrznych
                    // potem dodaj do zewnętrznych w vertexToTree - powinno obsłużyć listki
                    vertexToTree[a].first = nullptr;
                    vertexToTree[b].first = nullptr;
                    vertexToTree[aL] = {newNode, Side::Left};
                    vertexToTree[bR] = {newNode, Side::Right};
                    if (!aIsLeaf) {
                        cornerVertices.erase(a);
                    }
                    if (!bIsLeaf) {
                        cornerVertices.erase(b);
                    }
                }
            }
            shared_ptr<Node> order = vertexToTree[*cornerVertices.begin()].first;
            vector<int> result;
            result.reserve(n);
            result.push_back(centralVertex);
            order->dumpOrderly(result);
            long length = getHamiltonianLength(result);
            if (length < resultLength) {
                resultLength = length;
                bestResult = move(result);
            }
        }
        for (int v : bestResult) {
            cout << v << ' ';
        }
        cout << '\n' << resultLength << '\n';
        /*
         * algo:
         * zrób koniczyne (po jednym wierzchołku)
         * posortuj wszystkie krawędzie (nie dotykające środkowego) od najbardziej zaoszczędzającej
         * weź następną krawędź:
         * 1) można połączyć - połącz
         * 2) oba wierzchołki nie na końcach - odrzuć
         * 3) jeden wierzchołek nie na końcu:
         *  a) jest jeszcze trochę nieprzetworzonych krawędzi z tym wierzchołkiem - odrzuć
         *  b) nie ma już krawędzi z tym wierzchołkiem - przejdz po wszystkich listkach i dodaj w najlepsze miejsce
         *
         *  łączenie:
         *  - drzewo:
         *   liść - wierzchołek
         *   węzeł wewnętrzny - czy kolejność odwrócona, dwoje dzieci (lewe, prawe)
         *   serializacja do porządku inorder uwzględniając odwracanie kolejności w niektórych węzłach
         *  - wierzchołek -> lewy(drzewo)|prawy(drzewo)|wewnątrz
         *  - iterowanie po zbiorze skrajnych wierzchołków
         */
    }
    return 0;
}