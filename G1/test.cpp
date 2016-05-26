/* Opcje kompilacji:
   g++ test.cpp -otest -lCGAL -lgmp -frounding-math   */

#include <CGAL/Exact_predicates_inexact_constructions_kernel.h>
#include <CGAL/Delaunay_triangulation_2.h>
#include <CGAL/Triangulation_vertex_base_with_info_2.h>
#include <CGAL/Point_set_2.h>

#include <vector>
#include <iostream>
#include <algorithm>
#include <iterator>

using namespace std;


//jądro obliczeń arytmetyczych
typedef CGAL::Exact_predicates_inexact_constructions_kernel K;

//opisy wierzchołków 
typedef CGAL::Triangulation_vertex_base_with_info_2<int, K> Vb;

//reprezentacja triangulacji (ściany i wierzchołki)
typedef CGAL::Triangulation_data_structure_2<Vb> Tds;

//reprezentacja grafu Delaunaya           
//Point_set_2 jest klasą potomną Delaunay_triangulation_2  
//zawierającą dodatkowe metody, m.in. nearest_neighbors()
typedef CGAL::Delaunay_triangulation_2<K, Tds> Delaunay0;
typedef CGAL::Point_set_2<K, Tds> Delaunay;

typedef Delaunay::Point Point;                 //punkt grafu Delaunay'a       
typedef Delaunay::Edge_iterator Edge_iterator; //iterator po krawedziach grafu Delaunaya
typedef Delaunay::Vertex_handle Vertex_handle; //iterator po punktach grafu Delaunaya



int main()
{
    Delaunay T;
    vector<pair<Point, int> > points;
    int n;
    double x, y;

    //Wczytanie punktow
    cin >> n;
    for (int i = 0; i < n; i++) {
        cin >> x >> y;
        points.push_back(make_pair(Point(x, y), i));
    }
    T.insert(points.begin(), points.end());

    //Dostep do punktów
    cout << "Pierwszy punkt: " << points[0].first.x() << " ";
    cout << points[0].first.y() << endl;



    //Wypisanie punktów - wierzchołków grafu Delaunaya
    Delaunay::Finite_vertices_iterator vit;    //bez punnktu nieskończonego

    for (vit = T.finite_vertices_begin(); vit != T.finite_vertices_end(); ++vit)
        cout << vit->info() << ": " << vit->point() << endl;
    cout << endl;



    //Wypisanie sasiedów każdego wierzchołka
    Delaunay::Vertex_circulator vc, done;
    for (vit = T.finite_vertices_begin(); vit != T.finite_vertices_end(); ++vit) {
        cout << "Sasiedzi wierzcholka " << vit->info() << ":  ";
        vc = vit->incident_vertices();
        done = vc;
        if (vc != 0) {
            do {
                if (T.is_infinite(vc)) {
                    continue;
                }
                cout << vc->info() << " ";
            } while (++vc != done);
            cout << endl;
        }
    }


    //Wypukla otoczka
    cout << "Wypukla otoczka" << endl;
    vc = T.incident_vertices(T.infinite_vertex()), done = vc;
    if (vc != 0) {
        do {
            cout << vc->info() << ": " << vc->point() << endl;
        } while (++vc != done);
    }


    //Wypisywanie najbliższych sąsiadów
    cout << "Najbliżsi sąsiedzi" << endl;

    for (vit = T.finite_vertices_begin(); vit != T.finite_vertices_end(); ++vit) {
        vector<Vertex_handle> L;
        cout << vit->info() << " :";
        T.nearest_neighbors(vit, 4 + 1, back_inserter(L));      //łącznie z elementem vit

        for (int i = 0; i < L.size(); i++)
            cout << " " << L[i]->info();
        cout << "\n";
    }

    points.clear();
    T.clear();
    return 0;
}