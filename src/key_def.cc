#include "key_def.h"
#include "tuple.h"

int
tuple_compare_with_key(struct tuple *tuple, int key, key_def *key_def)
{
	return tuple->data[*key_def] - key;
}

int
tuple_compare(struct tuple *tuple_a, struct tuple *tuple_b, key_def *key_def) {
    return tuple_a->data[*key_def] - tuple_b->data[*key_def];
}

uint32_t
tuple_hash(struct tuple *tuple, key_def *key_def)
{
    return tuple->data[*key_def];
}
