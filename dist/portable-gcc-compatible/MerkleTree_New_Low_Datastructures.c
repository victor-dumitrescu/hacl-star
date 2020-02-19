/* MIT License
 *
 * Copyright (c) 2016-2020 INRIA, CMU and Microsoft Corporation
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */


#include "MerkleTree_New_Low_Datastructures.h"

/* SNIPPET_START: hash_dummy */

uint8_t *hash_dummy(uint32_t uu____14)
{
  return NULL;
}

/* SNIPPET_END: hash_dummy */

/* SNIPPET_START: hash_r_alloc */

uint8_t *hash_r_alloc(uint32_t s)
{
  KRML_CHECK_SIZE(sizeof (uint8_t), s);
  uint8_t *buf = KRML_HOST_CALLOC(s, sizeof (uint8_t));
  return buf;
}

/* SNIPPET_END: hash_r_alloc */

/* SNIPPET_START: hash_r_free */

void hash_r_free(uint32_t uu____212, uint8_t *v1)
{
  KRML_HOST_FREE(v1);
}

/* SNIPPET_END: hash_r_free */

/* SNIPPET_START: hash_copy */

void hash_copy(uint32_t s, uint8_t *src, uint8_t *dst)
{
  memcpy(dst, src, s * sizeof (src[0U]));
}

/* SNIPPET_END: hash_copy */

/* SNIPPET_START: copyable__uint32_t__uint8_t__tags */

#define Cpy 0

/* SNIPPET_END: copyable__uint32_t__uint8_t__tags */

typedef uint8_t copyable__uint32_t__uint8_t__tags;

/* SNIPPET_START: copyable__uint32_t__uint8_t_ */

typedef void (*copyable__uint32_t__uint8_t_)(uint32_t x0, uint8_t *x1, uint8_t *x2);

/* SNIPPET_END: copyable__uint32_t__uint8_t_ */

/* SNIPPET_START: hcpy */

void (*hcpy(uint32_t hsz))(uint32_t x0, uint8_t *x1, uint8_t *x2)
{
  return hash_copy;
}

/* SNIPPET_END: hcpy */

/* SNIPPET_START: hash_vec_dummy */

LowStar_Vector_vector_str___uint8_t_
hash_vec_dummy(LowStar_Regional_regional__uint32_t__uint8_t_ uu____471)
{
  return
    ((LowStar_Vector_vector_str___uint8_t_){ .sz = (uint32_t)0U, .cap = (uint32_t)0U, .vs = NULL });
}

/* SNIPPET_END: hash_vec_dummy */

/* SNIPPET_START: alloc_reserve___uint8_t_ */

static LowStar_Vector_vector_str___uint8_t_ alloc_reserve___uint8_t_(uint32_t len, uint8_t *ia)
{
  KRML_CHECK_SIZE(sizeof (uint8_t *), len);
  uint8_t **buf = KRML_HOST_MALLOC(sizeof (uint8_t *) * len);
  for (uint32_t _i = 0U; _i < len; ++_i)
    buf[_i] = ia;
  return ((LowStar_Vector_vector_str___uint8_t_){ .sz = (uint32_t)0U, .cap = len, .vs = buf });
}

/* SNIPPET_END: alloc_reserve___uint8_t_ */

/* SNIPPET_START: LowStar_Regional_rg_dummy___uint8_t__uint32_t */

uint8_t
*LowStar_Regional_rg_dummy___uint8_t__uint32_t(
  LowStar_Regional_regional__uint32_t__uint8_t_ rg
)
{
  return rg.dummy(rg.state);
}

/* SNIPPET_END: LowStar_Regional_rg_dummy___uint8_t__uint32_t */

/* SNIPPET_START: hash_vec_r_alloc */

LowStar_Vector_vector_str___uint8_t_
hash_vec_r_alloc(LowStar_Regional_regional__uint32_t__uint8_t_ s)
{
  return
    alloc_reserve___uint8_t_((uint32_t)1U,
      LowStar_Regional_rg_dummy___uint8_t__uint32_t(s));
}

/* SNIPPET_END: hash_vec_r_alloc */

/* SNIPPET_START: LowStar_Vector_free___uint8_t_ */

void LowStar_Vector_free___uint8_t_(LowStar_Vector_vector_str___uint8_t_ vec)
{
  KRML_HOST_FREE(vec.vs);
}

/* SNIPPET_END: LowStar_Vector_free___uint8_t_ */

/* SNIPPET_START: hash_vec_r_free */

void
hash_vec_r_free(
  LowStar_Regional_regional__uint32_t__uint8_t_ uu____709,
  LowStar_Vector_vector_str___uint8_t_ v1
)
{
  LowStar_Vector_free___uint8_t_(v1);
}

/* SNIPPET_END: hash_vec_r_free */
