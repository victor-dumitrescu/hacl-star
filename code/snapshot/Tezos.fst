module Tezos

open FStar.HyperStack
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer


let utils_secure_compare b1 b2 len =
  Hacl.Utils.secure_compare b1 b2 len

let curve25519_51_scalarmult shared my_priv their_pub =
  Hacl.Curve25519_51.scalarmult shared my_priv their_pub

let curve25519_51_ecdh shared my_priv their_pub =
  Hacl.Curve25519_51.ecdh shared my_priv their_pub

let crypto_box_detached c tag m mlen n pk sk =
  Hacl.NaCl.crypto_box_detached c tag m mlen n pk sk

let crypto_box_open_detached m c tag mlen n pk sk =
  Hacl.NaCl.crypto_box_open_detached m c tag mlen n pk sk

let crypto_box_easy c m mlen n pk sk =
  Hacl.NaCl.crypto_box_easy c m mlen n pk sk

let crypto_box_open_easy m c clen n pk sk =
  Hacl.NaCl.crypto_box_open_easy m c clen n pk sk

let blake2b_init hash kk k nn =
  Hacl.Blake2b.blake2b_init hash kk k nn

let blake2b_update_block hash prev d =
  Hacl.Blake2b.blake2b_update_block hash prev d

let blake2b_update_last hash prev len last =
  Hacl.Blake2b.blake2b_update_last hash prev len last

let blake2b_finish output hash nn =
  Hacl.Blake2b.blake2b_finish output hash nn

let blake2b nn output ll d kk k =
  Hacl.Blake2b.blake2b nn output ll d kk k
