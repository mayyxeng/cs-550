#include "ct-verif.h"

void copy_subarray_wrapper(uint8_t *out, const uint8_t *in,
		uint32_t len, uint32_t l_idx, uint32_t sub_len) {

      public_in(__SMACK_value(out));
      public_in(__SMACK_value(in));
      public_in(__SMACK_value(len));
      public_in(__SMACK_value(sub_len));
      copy_subarray(out, in, len, l_idx, sub_len);
}