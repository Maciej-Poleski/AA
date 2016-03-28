#include <iostream>
#include <random>

using namespace std;

int main()
{
    mt19937 engine(time(0));
    uniform_real_distribution<double> coordDist(-100, 100);
    int z = 1;
    cout << z << '\n';
    while (z--) {
        int n = 10000;
        cout << n << '\n';
        for (int i = 0; i < n; ++i) {
            cout << coordDist(engine) << ' ' << coordDist(engine) << '\n';
        }
    }
    return 0;
}