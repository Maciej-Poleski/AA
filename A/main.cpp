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
    const int nbNeighbors = 20;
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

static void buildMst()
{
    typedef pair<int, int> Edge;
    unordered_set<Edge> edgesSeen;
    vector<pair<Edge, int>> edges;
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
    for (auto &e : edges) {
        if (fu.tryUnion(e.first.first, e.first.second)) {
            addEdgeToFormerMst(e.first.first, e.first.second);
            nbComponents -= 1;
            if (nbComponents == 1) {
                break;
            }
        }
    }
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

static void crippleMst()
{
    assert(collectedLeaves.size() > 0);
    if (collectedLeaves[0].first == 0) {
        // Zebrana informacja dla korzenia nie jest poprawna - popraw
        collectedLeaves[0].second = FormerMst[0][0].destination;
    }
    for (const auto &p: collectedLeaves) {
        // drzewo może być jedną krawędzią (n=2)
        if (FormerMst[p.first].size() % 2 == 1) {
            addEdgeToFormerMst(p.first, p.second);
        }
    }
#ifdef DEBUG
    for (int i = 0; i < n; ++i) {
        assert(FormerMst[i].size() > 1);
    }
#endif
}

static vector<int> collectOddVertices()
{
    vector<int> result;
    for (int i = 0; i < n; ++i) {
        if (FormerMst[i].size() % 2 == 1) {
            result.push_back(i);
        }
    }
    return result;
}

class PriorityQueue
{
    unordered_map<int, int> realDistances;
    priority_queue<pair<int, int>> queue; // {stara_waga, indeks}

public:
    PriorityQueue(const list<int> &hamiltonianCycle, const vector<int> &oddVertices);

    int top(); // {indeks, odległość}

    bool empty();

    int pop();

    void update(int index, int newDistance);

private:
    void skipObsolete();
};

PriorityQueue::PriorityQueue(const list<int> &hamiltonianCycle, const vector<int> &oddVertices)
{
    unordered_set<int> interestingVertices(oddVertices.begin(), oddVertices.end());
    for (auto v : hamiltonianCycle) {
        interestingVertices.erase(v);
    }
    vector<pair<int, int>> distancesForHeap;
    {
        for (int i = 0; i < n; ++i) {
            if (interestingVertices.find(i) == interestingVertices.end()) {
                continue;
            }
            realDistances[i] = numeric_limits<int>::max(); // skoro euclid() zwraca int, to powinno wystarczyć
        }
    }
    // skanuje cały cykl i aktualizuje wstępne odległości
    for (auto v : hamiltonianCycle) {
        for (auto u : G[v]) {
            if (interestingVertices.count(u) == 0) {
                continue;
            }
            realDistances[u] = min(realDistances[u], euclid(u, v));
        }
    }
    for (const auto &p : realDistances) {
        distancesForHeap.emplace_back(p.second, p.first);
    }
    decltype(queue) q(less<pair<int, int >> (), move(distancesForHeap));
    queue.swap(q);
}

void PriorityQueue::skipObsolete()
{
    for (; !queue.empty();) {
        auto t = queue.top();
        assert(realDistances.count(t.second) == 1);
        auto rd = realDistances[t.second];
        if (rd == t.first) {
            return;
        }
        assert(rd < t.first);
        queue.pop();
        queue.push(make_pair(rd, t.second)); // aktualizacja
    }
}

int PriorityQueue::top()
{
    assert(!empty());
    skipObsolete();
#ifdef DEBUG
    int bestDist = numeric_limits<int>::min();
    int selection;
    for (auto &p : realDistances) {
        if (bestDist < p.second) {
            bestDist = p.second;
            selection = p.first;
        }
    }
    assert(bestDist == queue.top().first);
#endif
    return queue.top().second;
}

bool PriorityQueue::empty()
{
    skipObsolete();
    return queue.empty();
}

int PriorityQueue::pop()
{
    assert(!empty());
    int t = top(); // skipObsolete
    realDistances.erase(t);
    queue.pop();
    return t;
}

void PriorityQueue::update(int index, int newDistance)
{
    auto i = realDistances.find(index);
    if (i != realDistances.end()) {
        if (i->second > newDistance) {
            //realDistances.insert(i, make_pair(index, newDistance));
            realDistances[index] = newDistance;
            assert(realDistances[index] == newDistance);
            // queue.push(make_pair(newDistance, index));
            // poprawiaj leniwie
        }
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

static void extendToEuler()
{
    // TODO: kiepski szkielet?
    const auto oddVertices = collectOddVertices();    // indeksy
    list<int> hamiltonianCycle;
    // otoczka wypukła
    {
        vector<Point> rawPoints;
        unordered_map<Point, int> oddPointToIdx;
        for (auto v : oddVertices) {
            rawPoints.push_back(input[v]);
            oddPointToIdx[input[v]] = v;
        }
        vector<Point> convexHull;
        CGAL::convex_hull_2(rawPoints.begin(), rawPoints.end(), back_inserter(convexHull));
        for (const auto &p : convexHull) {
            hamiltonianCycle.push_back(oddPointToIdx[p]);
        }
    }
#ifdef DEBUG
    list<int> referenceCycle = hamiltonianCycle;
    {
        vector<bool> available(n, false);
        for (auto v : oddVertices) {
            available[v] = true;
        }
        vector<int> distances(n, numeric_limits<int>::max());
        for (auto v : referenceCycle) {
            available[v] = false;
            for (int i = 0; i < n; ++i) {
                //for (auto i : G[v]) {
                distances[i] = min(distances[i], euclid(v, i));
            }
        } // FIXME: ŹLE - uwzględniać tylko wierzchołki z grafu kandydatów
        for (int rest = oddVertices.size() - hamiltonianCycle.size(); rest > 0; --rest) {
            assert(oddVertices.size() > referenceCycle.size());
            int dist = -1;
            int selected = -1;
            for (auto i : oddVertices) {
                if (available[i] && dist < distances[i]) {
                    dist = distances[i];
                    selected = i;
                }
            }
            assert(selected != -1);
            // FIXME: rozwiązanie jest niejednoznaczne - przepleść z algo na kopcu i sprawdzać spójność z brutem
            int cost = numeric_limits<int>::max();
            auto position = referenceCycle.begin();
            for (auto i = referenceCycle.begin(), e = referenceCycle.end(); i != e; ++i) {
                auto j = i;
                ++j;
                const int propositionCost = euclid(*i, selected) + euclid(selected, *j) - euclid(*i, *j);
                if (cost > propositionCost) {
                    cost = propositionCost;
                    position = j;
                }
            }
            if (cost > euclid(referenceCycle.back(), selected) + euclid(selected, referenceCycle.front()) -
                       euclid(referenceCycle.back(), referenceCycle.front())) {
                position = referenceCycle.begin();
            }
            referenceCycle.insert(position, selected);
            available[selected] = false;
            for (int i : oddVertices) {
                //for (auto i : G[selected]) {
                distances[i] = min(distances[i], euclid(selected, i));
            }
        }
    }
    hamiltonianCycle = move(referenceCycle);
#else
    // rozszerzenie otoczki na pozostałe wierzchołki
    PriorityQueue pq(hamiltonianCycle, oddVertices);
    while (!pq.empty()) {
        auto newVertex = pq.pop();
        auto i = hamiltonianCycle.begin();
        auto j = i;
        ++j;
        auto selectedPosition = i;
        int minDistance = numeric_limits<int>::max();
        for (auto e = hamiltonianCycle.end(); j != e; ++i, ++j) {
            // w sumie krawędzie z otoczki mogą nie istnieć w grafie kandydatów...
            int dist_ = euclid(*i, newVertex) + euclid(newVertex, *j) - euclid(*i, *j);
            if (minDistance > dist_) {
                minDistance = dist_;
                selectedPosition = j;
            }
        }
        j = hamiltonianCycle.begin();
        if (minDistance > euclid(*i, newVertex) + euclid(newVertex, *j) - euclid(*i, *j)) {
            hamiltonianCycle.push_back(newVertex);
        } else {
            hamiltonianCycle.insert(selectedPosition, newVertex);
#ifdef DEBUG
            {
                auto k = selectedPosition;
                --k;
                assert(*k == newVertex);
            }
#endif
        }
        // aktualizacja odległości
        for (auto v : G[newVertex]) {
            pq.update(v, euclid(newVertex, v)); // zaaktualizuje jeżeli przybliża
        }
    }
#endif
    assert(hamiltonianCycle.size() % 2 == 0);
    assert(hamiltonianCycle.size() == oddVertices.size());
#ifdef DEBUG
    {
        vector<int> a(oddVertices.begin(), oddVertices.end());
        vector<int> b(hamiltonianCycle.begin(), hamiltonianCycle.end());
        sort(a.begin(), a.end());
        sort(b.begin(), b.end());
        assert(a == b);
    };
#endif
    // wybór lepszego skojarzenia
    long even = 0, odd = 0;
    for (auto i = hamiltonianCycle.begin(), e = hamiltonianCycle.end(); i != e;) {
        int u = *i++;
        int v = *i++;
        even += euclid(u, v);
    }
    for (auto i = hamiltonianCycle.begin(), e = hamiltonianCycle.end(); ;) {
        int u = *++i;
        ++i;
        if (i == e) {
            break;
        }
        int v = *i;
        odd += euclid(u, v);
    }
    odd += euclid(hamiltonianCycle.back(), hamiltonianCycle.front());
    auto i = hamiltonianCycle.begin();
    if (odd < even) {
        hamiltonianCycle.push_back(hamiltonianCycle.front());
        ++i;
    }
#ifdef DEBUG
    long cost = 0;
#endif
    // rozszerzenie FormerMst do grafu Eulerowskiego
    for (auto e = hamiltonianCycle.end(); i != e;) {
        // i, ++i - krawędź
        int u = *i++;
        int v = *i++;
        addEdgeToFormerMst(u, v);
#ifdef DEBUG
        cost += euclid(u, v);
#endif
    }
#ifdef DEBUG
    assert(cost == min(odd, even));
#endif
}

static mt19937 randomEngine(time(0));

static vector<vector<unsigned>> nextEdge;
static vector<int> result1;
static vector<bool> usedVertices1;

static void walk(int v)
{
    assert(v >= 0);
    assert(v < n);
    while (nextEdge[v].back() < FormerMst[v].size()) {
        Edge nextVertex = FormerMst[v][nextEdge[v].back()];
        if (nextVertex.destination == -1) {
            nextEdge[v].pop_back();
            continue;
        }
        assert(nextVertex.destination == FormerMst[v][nextEdge[v].back()].destination);
        removeEdgeFromFormerMst(v, nextVertex.destination, nextEdge[v].back());
        nextEdge[v].pop_back();
        walk(nextVertex.destination);
        if (!usedVertices1[nextVertex.destination]) {
            usedVertices1[nextVertex.destination] = true;
            result1.push_back(nextVertex.destination);
        }
    }
}

static long getHamiltonianLength(const vector<int> &hamiltonian)
{
    long result = 0;
    for (unsigned i = 1; i < hamiltonian.size(); ++i) {
        result += euclid(hamiltonian[i - 1], hamiltonian[i]);
    }
    result += euclid(hamiltonian.back(), hamiltonian.front());
    return result;
}

static pair<vector<int>, long> getHamiltonian(int v)
{
    nextEdge.assign(n, {});
    for (int i = 0; i < n; ++i) {
        for (int j = 0; j < FormerMst[i].size(); ++j) {
            nextEdge[i].push_back(j);
        }
        shuffle(nextEdge[i].begin(), nextEdge[i].end(), randomEngine);
        assert(FormerMst[i].size() % 2 == 0);
        assert(FormerMst[i].size() > 0);
    }
    result1.clear();
    result1.reserve(n);
    result1.push_back(v);
    usedVertices1.assign(n, false);
    usedVertices1[v] = true;
    auto copy(FormerMst);
    walk(v);
    assert(result1.size() == n);
    FormerMst = move(copy);
    long l1 = getHamiltonianLength(result1);
    return {result1, l1};

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
        buildMst();
        collectedLeaves.clear();
        collectLeaves();
        crippleMst();
        extendToEuler();
        uniform_int_distribution<int> startVertex(0, n - 1);
        auto hamiltonianCycle = getHamiltonian(startVertex(randomEngine));
        for (int i = 1; i < 50; ++i) {
            auto candidate = getHamiltonian(startVertex(randomEngine));
            if (candidate.second < hamiltonianCycle.second) {
                swap(candidate, hamiltonianCycle);
            }
        }
        for (auto v : hamiltonianCycle.first) {
            cout << v << ' ';
        }
        cout << '\n' << hamiltonianCycle.second << '\n';
    }
    return 0;
}