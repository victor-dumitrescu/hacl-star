module Tezos

open FStar.HyperStack
open FStar.HyperStack.All
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

module LSeq = Lib.Sequence
module B = LowStar.Buffer
module LBS = Lib.ByteSequence


val utils_secure_compare:
    b1: buffer uint8
  -> b2: buffer uint8
  -> len: size_t{v len = length b1 /\ v len = length b2} ->
  Stack bool
    (requires fun h -> live h b1 /\ live h b2)
    (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == LBS.lbytes_eq #(v len) (B.as_seq #uint8 h0 b1) (B.as_seq #uint8 h0 b2))

val curve25519_51_scalarmult:
    shared:lbuffer uint8 32ul
  -> my_priv:lbuffer uint8 32ul
  -> their_pub:lbuffer uint8 32ul ->
  Stack unit
    (requires fun h0 ->
      live h0 shared /\ live h0 my_priv /\ live h0 their_pub /\
      disjoint shared my_priv /\ disjoint shared their_pub)
    (ensures  fun h0 _ h1 -> modifies (loc shared) h0 h1 /\
      as_seq h1 shared == Spec.Curve25519.scalarmult (as_seq h0 my_priv) (as_seq h0 their_pub))

val curve25519_51_ecdh:
    shared:lbuffer uint8 32ul
  -> my_priv:lbuffer uint8 32ul
  -> their_pub:lbuffer uint8 32ul ->
  Stack bool
    (requires fun h0 ->
      live h0 shared /\ live h0 my_priv /\ live h0 their_pub /\
      disjoint shared my_priv /\ disjoint shared their_pub)
    (ensures  fun h0 r h1 -> modifies (loc shared) h0 h1 /\
      as_seq h1 shared == Spec.Curve25519.scalarmult (as_seq h0 my_priv) (as_seq h0 their_pub)
      /\ (not r == Lib.ByteSequence.lbytes_eq #32 (as_seq h1 shared) (Lib.Sequence.create 32 (u8 0))))

// #set-options "--max_fuel 50 --max_fuel 0 --max_ifuel 0"

val crypto_box_detached:
    c:buffer uint8
  -> tag:lbuffer uint8 16ul
  -> m:buffer uint8
  -> mlen:size_t{length c = v mlen /\ length m = v mlen}
  -> n:lbuffer uint8 24ul
  -> pk:lbuffer uint8 32ul
  -> sk:lbuffer uint8 32ul ->
  Stack size_t
  (requires fun h ->
    live h c /\ live h m /\ live h sk /\ live h pk /\ live h n /\ live h tag /\
    disjoint tag c /\ eq_or_disjoint (m <: lbuffer uint8 mlen) (c <: lbuffer uint8 mlen) /\
    disjoint tag m /\ disjoint n m /\ disjoint n c)
  (ensures  fun h0 r h1 -> modifies2 c tag h0 h1 /\
   (let tag_cipher = Spec.Box.box_detached (as_seq h0 sk) (as_seq h0 pk) (as_seq h0 n) (as_seq #MUT #uint8 #mlen h0 m) in
    match r with
    | 0ul -> Some? tag_cipher /\ (let (tag_s, cipher_s) = Some?.v tag_cipher in (as_seq h1 tag, as_seq #MUT #uint8 #mlen h1 c) == (tag_s, cipher_s))
    | _ -> None? tag_cipher))

val crypto_box_open_detached:
    m:buffer uint8
  -> c:buffer uint8
  -> tag:lbuffer uint8 16ul
  -> mlen:size_t{length c = v mlen /\ length m = v mlen}
  -> n:lbuffer uint8 24ul
  -> pk:lbuffer uint8 32ul
  -> sk:lbuffer uint8 32ul ->
  Stack size_t
  (requires fun h ->
    live h c /\ live h m /\ live h pk /\ live h sk /\ live h n /\ live h tag /\
    disjoint tag c /\ eq_or_disjoint (m <: lbuffer uint8 mlen) (c <: lbuffer uint8 mlen) /\
    disjoint tag m /\ disjoint n m /\ disjoint n c)
  (ensures  fun h0 r h1 -> modifies1 m h0 h1 /\
   (let msg = Spec.Box.box_open_detached (as_seq h0 pk) (as_seq h0 sk) (as_seq h0 n) (as_seq h0 tag) (as_seq #MUT #uint8 #mlen h0 c) in
    match r with
    | 0ul -> Some? msg /\ as_seq #MUT #uint8 #mlen h1 m == Some?.v msg
    | _ -> None? msg))

val crypto_box_easy:
    c:buffer uint8
  -> m:buffer uint8
  -> mlen:size_t{length c = v mlen + 16 /\ length m = v mlen}
  -> n:lbuffer uint8 24ul
  -> pk:lbuffer uint8 32ul
  -> sk:lbuffer uint8 32ul ->
  Stack size_t
  (requires fun h ->
    live h c /\ live h m /\ live h sk /\ live h pk /\ live h n /\
    disjoint m c /\ disjoint n m /\ disjoint n c)
  (ensures  fun h0 r h1 -> modifies1 c h0 h1 /\
    (let cipher = Spec.Box.box_easy (as_seq h0 sk) (as_seq h0 pk) (as_seq h0 n) (as_seq #MUT #uint8 #mlen h0 m) in
    match r with
    | 0ul -> Some? cipher /\ as_seq #MUT #uint8 #(mlen +! 16ul) h1 c == Some?.v cipher
    | _ -> None? cipher))

#set-options "--z3rlimit 100"

val crypto_box_open_easy:
    m:buffer uint8
  -> c:buffer uint8
  -> clen:size_t{length c = v clen /\ v clen = length m + 16}
  -> n:lbuffer uint8 24ul
  -> pk:lbuffer uint8 32ul
  -> sk:lbuffer uint8 32ul ->
  Stack size_t
  (requires fun h ->
    live h c /\ live h m /\ live h pk /\ live h sk /\ live h n /\
    disjoint m c /\ disjoint m n /\ disjoint c n)
  (ensures fun h0 r h1 -> modifies1 m h0 h1 /\
   (let msg = Spec.Box.box_open_easy (as_seq h0 pk) (as_seq h0 sk) (as_seq h0 n) (as_seq #MUT #uint8 #clen h0 c) in
    match r with
    | 0ul -> Some? msg /\ as_seq #MUT #uint8 #(clen -! 16ul) h1 m == Some?.v msg
    | _ -> None? msg))

let hash_wp = lbuffer uint64 (size 8)
let block_p = lbuffer uint8 (size 128)

val blake2b_init:
    hash: hash_wp
  -> kk: size_t{v kk <= 64}
  -> k: lbuffer uint8 kk
  -> nn: size_t{1 <= v nn /\ v nn <= 64} ->
  Stack unit
    (requires (fun h -> live h hash
                   /\ live h k
                   /\ disjoint hash k
                   /\ disjoint k hash))
    (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                         /\ h1.[|hash|] == Spec.Blake2.blake2_init Spec.Blake2.Blake2B (v kk) h0.[|k|] (v nn)))

val blake2b_update_block:
    hash:hash_wp
  -> prev:uint128{uint_v prev <= Spec.Blake2.max_limb Spec.Blake2.Blake2B}
  -> d:block_p ->
  Stack unit
    (requires (fun h -> live h hash
                   /\ live h d
                   /\ disjoint hash d))
    (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                         /\ h1.[|hash|] == Spec.Blake2.blake2_update_block Spec.Blake2.Blake2B (uint_v prev) h0.[|d|] h0.[|hash|]))

val blake2b_update_last:
    hash: hash_wp
  -> prev: uint128{uint_v prev <= Spec.Blake2.max_limb Spec.Blake2.Blake2B}
  -> len: size_t{v len <= Spec.Blake2.size_block Spec.Blake2.Blake2B}
  -> last: lbuffer uint8 len ->
  Stack unit
    (requires (fun h -> live h hash
                   /\ live h last
                   /\ disjoint hash last))
    (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                         /\ h1.[|hash|] == Spec.Blake2.blake2_update_last Spec.Blake2.Blake2B (uint_v prev) (v len) h0.[|last|] h0.[|hash|]))

val blake2b_finish:
    nn: size_t{1 <= v nn /\ v nn <= 64}
  -> output: lbuffer uint8 nn
  -> hash: hash_wp ->
  Stack unit
    (requires (fun h -> live h hash
                   /\ live h output
                   /\ disjoint output hash
                   /\ disjoint hash output))
    (ensures  (fun h0 _ h1 -> modifies1 output h0 h1
                         /\ h1.[|output|] == Spec.Blake2.blake2_finish Spec.Blake2.Blake2B h0.[|hash|] (v nn)))

val blake2b:
    nn:size_t{1 <= v nn /\ v nn <= 64}
  -> output: lbuffer uint8 nn
  -> ll: size_t
  -> d: lbuffer uint8 ll
  -> kk: size_t{v kk <= 64 /\ (if v kk = 0 then v ll < pow2 128 else v ll + 128 < pow2 128)}
  -> k: lbuffer uint8 kk ->
  Stack unit
    (requires (fun h -> live h output
                   /\ live h d
                   /\ live h k
                   /\ disjoint output d
                   /\ disjoint output k))
    (ensures  (fun h0 _ h1 -> modifies (loc output) h0 h1
                         /\ h1.[|output|] == Spec.Blake2.blake2b h0.[|d|] (v kk) h0.[|k|] (v nn)))
