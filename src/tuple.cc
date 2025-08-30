#include "tuple.h"
#include <string>
#include <cstring>
#include <numeric>

std::string
tuple_str(const struct tuple *tuple)
{
    if (tuple == nullptr)
        return std::string("NULL");

    if (tuple->data.empty())
        return std::string("{}");

    return std::accumulate(
        tuple->data.begin() + 1,
        tuple->data.end(),
        "{" + std::to_string(tuple->data[0]),
        [](const std::string& a, int b) {
            return a + ", " + std::to_string(b);
        }
    ) + "}";
}
