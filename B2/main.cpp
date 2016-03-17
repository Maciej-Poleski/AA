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

struct Edge
{
    int destination;    // -1 - skasowana
    int incidentIndex;
};

static int n;
static vector<Point> input;

static vector<vector<int>> G;   // graf kandydatów
static vector<vector<Edge>> FormerMst; // MST

static void addEdgeToFormerMst(int u, int v)
{
    assert(u >= 0);
    assert(v >= 0);
    assert(u < n);
    assert(v < n);
    FormerMst[u].push_back({v, FormerMst[v].size()});
    FormerMst[v].push_back({u, FormerMst[u].size() - 1});
    assert(FormerMst[u].back().destination == v);
    assert(FormerMst[v].back().destination == u);
    assert(FormerMst[u].back().incidentIndex == FormerMst[v].size() - 1);
    assert(FormerMst[v].back().incidentIndex == FormerMst[u].size() - 1);
}

static void removeEdgeFromFormerMst(int u, int v, unsigned index)
{
    assert(u >= 0);
    assert(v >= 0);
    assert(u < n);
    assert(v < n);
    assert(index < FormerMst[u].size());
    const Edge e = FormerMst[u][index];
    assert(v == e.destination);
    assert(v != -1);
    assert(e.incidentIndex >= 0);
    assert(e.incidentIndex < FormerMst[v].size());
    assert(FormerMst[u][index].destination == v);
    FormerMst[u][index].destination = -1;
    assert(FormerMst[v][e.incidentIndex].destination == u);
    FormerMst[v][e.incidentIndex].destination = -1;
}

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
    const int nbNeighbors = 2;
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

static pair<long, long> buildMst()
{
    typedef pair<int, int> Edge;
    unordered_set<Edge> edgesSeen;
    vector<pair<Edge, int>> edges;
    long weight = 0;
    assert(G.size() == n);
    for (int i = 0; i < n; ++i) {
        for (auto v:G[i]) {
            if (edgesSeen.count({v, i})) {
                continue;
            }
            edgesSeen.insert({i, v});
            edges.emplace_back(make_pair(i, v), euclid(i, v));
        }
    }
    sort(edges.begin(), edges.end(), [](const pair<Edge, int> &lhs, const pair<Edge, int> &rhs) {
        return lhs.second < rhs.second;
    });
    FindUnion fu(n);
    int nbComponents = n;
    FormerMst.assign(n, {});
    long lastEdge = -1;
    for (auto &e : edges) {
        if (fu.tryUnion(e.first.first, e.first.second)) {
            addEdgeToFormerMst(e.first.first, e.first.second);
            weight += e.second;
            nbComponents -= 1;
            if (nbComponents == 1) {
                lastEdge = e.second;
                break;
            }
        }
    }
    assert(lastEdge != -1);
    return {weight, lastEdge};
}

static vector<pair<int, int>> collectedLeaves;

static void collectLeaves(int v = 0, int p = -1)
{
    // Czemu to się NIE pętli?
    // Bo MST jest grafem acyklicznym
    if (FormerMst[v].size() == 1) {
        collectedLeaves.emplace_back(v, p);
    }
    for (auto &u: FormerMst[v]) {
        if (u.destination == p) {
            continue;
        }
        collectLeaves(u.destination, v);
    }
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

static int findEdge()
{
    int result = 0;
    for (const auto &p : collectedLeaves) {
        vector<int> edges;
        for (auto v : G[p.first]) {
            edges.push_back(euclid(p.first, v));
        }
        sort(edges.begin(), edges.end());
        assert(edges.size() > 1);
        result = max(result, edges[1]);
    }
    return result;
}

int main()
{
    //close(0);
    //open("/home/local/AA/A/testy/t00.in", O_RDONLY);
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
        auto mstWeightAndLastEdge = buildMst();
        collectedLeaves.clear();
        collectLeaves();
        long weight2 = findEdge();
        cout << mstWeightAndLastEdge.first + max(mstWeightAndLastEdge.second, weight2) << '\n';
    }
    return 0;
}