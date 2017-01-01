#define COLLECTION_PARTITON_DBG
#include "collection_partition.h"

using namespace std;

int main() {
    collection_partition<int> test[4];

    test[0].insert_new(8);
    test[0].insert_new(0);
    test[0].insert_new(4);
    test[1].insert_new(9);
    test[1].insert_new(1);
    test[1].insert_new(5);
    test[2].insert_new(10);
    test[2].insert_new(2);
    test[2].insert_new(6);
    test[3].insert_new(11);
    test[3].insert_new(3);
    test[3].insert_new(7);

    for (int i = 0; i < 4; ++i) {
        cout << test[i] << endl;
    }

    swap(test[0], test[3], 8);
    swap(test[1], test[3], 1);
    swap(test[2], test[3], 6);
}
