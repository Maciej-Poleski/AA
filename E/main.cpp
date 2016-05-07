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

static int euclid(Point A, Point B)
{
    double x = A.x() - B.x();
    double y = A.y() - B.y();
    return static_cast<int>(hypot(x, y) + .5);
}

//static void buildG()
//{
//    // static vector <vector<int>> G;   // graf kandydatów
//    const int nbNeighbors = 10;
//    G.resize(n);
//    Delaunay D;
//    vector <pair<Point, int>> delonePoints;
//    assert(input.size() == n);
//    for (int i = 0; i < n; ++i) {
//        delonePoints.push_back(make_pair(input[i], i));
//    }
//    D.insert(delonePoints.begin(), delonePoints.end());
//    vector <unordered_set<int>> Gproto(n);
//    for (auto i = D.finite_vertices_begin(), e = D.finite_vertices_end(); i != e; ++i) {
//        vector<int> neighbors;
//        auto vc = i->incident_vertices();
//        CGAL::Container_from_circulator<decltype(vc)> c(vc);
//        for (auto &v : c) {
//            if (!D.is_infinite(v.handle())) {
//                neighbors.push_back(v.info());
//            }
//        }
//        vector <Vertex_handle> near;
//        D.nearest_neighbors(i, 1 + nbNeighbors, back_inserter(near));
//        assert(near.size() >= min(nbNeighbors, n - 1));
//        for (auto &v : near) {
//            if ((!D.is_infinite(v)) && (v != i->handle())) {
//                neighbors.push_back(v->info());
//            }
//        }
//        assert(neighbors.size() >= min(nbNeighbors, n - 1));
//        Gproto[i->info()].insert(neighbors.begin(), neighbors.end());
//        for (auto &v:neighbors) {
//            Gproto[v].insert(i->info());
//        }
//    }
//    for (int i = 0; i < n; ++i) {
//#ifdef DEBUG
//        for (auto &v:Gproto[i]) {
//            assert(Gproto[v].find(i) != Gproto[v].end());
//        }
//#endif
//        G[i].assign(Gproto[i].begin(), Gproto[i].end());
//        assert(G[i].size() >= min(nbNeighbors, n - 1));
//    }
//}

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
        Point representant;
    public:
        void addPoint(int p)
        {
            points.push_back(p);
        }

        void construct()
        {
            chooseRepresentantPoint();
        }

        Point getRepresentant() const
        {
            return representant;
        }

        const vector<int> &getPoints() const
        {
            return points;
        }

        bool empty() const
        {
            return points.empty();
        }

    private:
        void chooseRepresentantPoint();
    };

    struct CellRelative
    {
        int distance = -1;
        int from, to;   // Identyfikator globalny (nie points-iterator)
    };

    vector<PlaneCell> cells;
    vector<CellRelative> distances;
    int k;

public:
    PlaneHierarchy(int k);

    list <metaCoords_t> chooseMetaCycle();

    list<int> choosePathForChunk(metaCoords_t before, metaCoords_t chunk, metaCoords_t after);

private:
    int encode(int x, int y) const
    {
        assert(x >= 0);
        assert(y >= 0);
        assert(x * k + y < k * k);
        return y * k + x;
    }

    int encode(metaCoords_t P) const
    {
        return encode(P.first, P.second);
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
    PlaneCell &getCellChecked(int x, int y);

    int euclid(metaCoords_t A, metaCoords_t B);

    int encodeMeta(metaCoords_t A, metaCoords_t B) const
    { return encode(B) * k * k + encode(A); }
};

PlaneHierarchy::PlaneHierarchy(int k) : cells(k * k), distances(k * k * k * k), k(k)
{
    double maxX = max_element(input.begin(), input.end(), [](const Point &lhs, const Point &rhs) {
        return lhs.x() < rhs.x();
    })->x();
    double maxY = max_element(input.begin(), input.end(), [](const Point &lhs, const Point &rhs) {
        return lhs.y() < rhs.y();
    })->y();
    double width = maxX / k;
    double height = maxY / k;
    for (int i = 0; i < input.size(); ++i) {
        int x = static_cast<int>(input[i].x() / width);
        int y = static_cast<int>(input[i].y() / height);
        getCellChecked(x, y).addPoint(i);
    }
    for (auto &c : cells) {
        c.construct();
    }
}

PlaneHierarchy::PlaneCell &PlaneHierarchy::getCellChecked(int x, int y)
{
    assert(x >= 0);
    assert(y >= 0);
    if (x >= k) {
        assert(x == k);
        x -= 1;
    }
    if (y >= k) {
        assert(y == k);
        y -= 1;
    }
    assert(x * k + y < k * k);
    return getCell(x, y);
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

int PlaneHierarchy::euclid(metaCoords_t A, metaCoords_t B)
{
    assert(!getCell(A).empty());
    assert(!getCell(B).empty());
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
        const auto &pointsA = getCell(A).getPoints(), &pointsB = getCell(B).getPoints();
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

list <metaCoords_t> PlaneHierarchy::chooseMetaCycle()
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
    for (auto p : result) {
        metaVertexInResult[encode(p.first, p.second)] = true;
    }
    while (true) {
        // wybierz najdalszy punkt
        int bestDistnace = -1;
        pair<metaCoord_t, metaCoord_t> P;
        for (int x = 0; x < k; ++x) {
            for (int y = 0; y < k; ++y) {
                if (metaVertexInResult[encode(x, y)] || getCell(x, y).empty()) {
                    continue;
                }
                int dist = numeric_limits<int>::max();
                for (auto p : result) {
                    auto newDist = euclid({x, y}, p);
                    if (newDist < dist) {
                        dist = newDist;
                    }
                }
                if (dist > bestDistnace) {
                    bestDistnace = dist;
                    P = {x, y};
                }
            }
        }
        if (bestDistnace == -1) {
            break; // wyczerpana pula meta punktów
        }
        // wstaw wybrany punkt P
        auto position = result.cbegin();
        int price = euclid(result.back(), P) + euclid(P, result.front()) - euclid(result.back(), result.front());
        for (auto j = result.cbegin(), i = j++; j != result.cend(); ++j, ++i) {
            int newPrice = euclid(*i, P) + euclid(P, *j) - euclid(*i, *j);
            if (newPrice < price) {
                price = newPrice;
                position = j;
            }
        }
        result.insert(position, P);
        metaVertexInResult[encode(P)] = true;
    }
    return result;
}

list<int> PlaneHierarchy::choosePathForChunk(metaCoords_t before, metaCoords_t chunk, metaCoords_t after)
{
    euclid(chunk, before); // potrzebny efekt uboczny - wskazanie wierzchołków "przejściowych"
    euclid(chunk, after);
    assert(distances[encodeMeta(chunk, before)].distance != -1);
    assert(distances[encodeMeta(chunk, after)].distance != -1);
    int begin = distances[encodeMeta(chunk, before)].from;
    int end = distances[encodeMeta(chunk, after)].from;
    list<int> result = {begin, end};
    if (begin == end) {
        result.pop_back();
    }
    list<int> remainingVertices;
    const vector<int> &pointsIndices = getCell(chunk).getPoints();
    for (int p : pointsIndices) {
        if ((p != begin) && (p != end)) {
            remainingVertices.push_back(p);
        }
    }
    assert(remainingVertices.size() == pointsIndices.size() - result.size());
    while (result.size() != pointsIndices.size()) {
        using ::euclid;
        // wybierz najdalszy od result
        auto nextVertexIdx = remainingVertices.begin();
        int maxDistFromResultSet = -1;
        for (auto candidate = remainingVertices.begin(), e = remainingVertices.end(); candidate != e; ++candidate) {
            int minDistToResultSet = numeric_limits<int>::max();
            for (int resultPoint : result) {
                int newDist = euclid(resultPoint, *candidate);
                if (newDist < minDistToResultSet) {
                    minDistToResultSet = newDist;
                }
            }
            if (minDistToResultSet > maxDistFromResultSet) {
                maxDistFromResultSet = minDistToResultSet;
                nextVertexIdx = candidate;
            }
        }
        int vertex = *nextVertexIdx;
        remainingVertices.erase(nextVertexIdx);
        // wstaw vertex w najlepsze miejsce
        auto position = result.cbegin();
        int price =
                euclid(result.back(), vertex) + euclid(vertex, result.front()) - euclid(result.back(), result.front());
        for (auto j = result.cbegin(), i = j++; j != result.cend(); ++j, ++i) {
            int newPrice = euclid(*i, vertex) + euclid(vertex, *j) - euclid(*i, *j);
            if (newPrice < price) {
                price = newPrice;
                position = j;
            }
        }
        result.insert(position, vertex);
    }
    return result;
}

template<typename DContainer, typename SContainer>
void copy(DContainer &dest, const SContainer &source)
{
    copy(source.begin(), source.end(), back_inserter(dest));
};

int main()
{
    close(0);
    open("/home/local/AA/E/testy/t00.in", O_RDONLY);
    ios_base::sync_with_stdio(false);
    int z;
    cin >> z;
    while (z--) {
        cin >> n;
        input.resize(n);
        for (auto &p:input) {
            cin >> p;
        }
        double minX = min_element(input.begin(), input.end(), [](const Point &lhs, const Point &rhs) {
            return lhs.x() < rhs.x();
        })->x();
        double minY = min_element(input.begin(), input.end(), [](const Point &lhs, const Point &rhs) {
            return lhs.y() < rhs.y();
        })->y();
        for (auto &p : input) {
            p = {p.x() - minX, p.y() - minY};
        }
        int k = static_cast<int>(sqrt(sqrt(n)));
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

        for (int v : result) {
            cout << v << ' ';
        }
        cout << '\n' << getHamiltonianLength(result.begin(), result.end()) << '\n';
    }
}