#include "tuple.h"
#include <string>
#include <cstring>
#include <numeric>

char *
tuple_str(struct tuple *tuple)
{
    if (tuple == nullptr) {
        char* result = new char[4];
        strcpy(result, "nil");
        return result;
    }
    if (tuple->data.empty()) {
        char* result = new char[3];
        strcpy(result, "{}");
        return result;
    }
    auto str = std::accumulate(
        tuple->data.begin() + 1,
        tuple->data.end(),
        "{" + std::to_string(tuple->data[0]),
        [](const std::string& a, int b) {
            return a + ", " + std::to_string(b);
        }
    ) + "}";
    char* result = new char[str.size() + 1];  // +1 для '\0'
    strcpy(result, str.c_str());
    return result;
}
