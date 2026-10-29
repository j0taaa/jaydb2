#ifndef JAYDB_FIELD_RECIPE_H
#define JAYDB_FIELD_RECIPE_H
#include "field.h"
/* Private component recipe. These words are raw components/existing children;
 * the NEW Term header is formed only in the held production leaf. */
struct jaydb_word192 { uint64_t payload, auxiliary, tag; };
enum jaydb_recipe_operation { JAYDB_RECIPE_WORD=0,JAYDB_RECIPE_PAK=1,JAYDB_RECIPE_CTR=2 };
struct jaydb_field_recipe {
  uint64_t operation,constructor_id,site_id,location,quantity;
  struct jaydb_field_wire wire;
  struct jayacct_u128 scope,ceiling,deadline;
  const struct jaydb_word192 *components;
  struct jaydb_word192 *const *destinations;
  uint64_t count;
  struct jaydb_word192 *header;
  uint64_t *claim;
  uint64_t claim_value;
  /* Optional durable aggregate receipts, already active and disjoint from
   * payload. Updated in the leaf so a guard longjmp immediately after return
   * cannot hide a real partial claim or a completed header. */
  uint64_t *completed_count,*claim_count;
};
/* Destinations/header/claim/records and audited explicit stack are already
 * active. Raw arena ensure precedes this call; claim is not performed there.
 * Length is rechecked from the original immutable wire. No callback/allocator
 * or library runs while held. The active window is not closed. */
uint64_t jaydb_field_recipe_stack_v3(void);
uint64_t jaydb_field_recipe_v3(const struct jaydb_field_recipe *,void *,uint64_t,
                              struct jaydb_field_result *);
#endif
