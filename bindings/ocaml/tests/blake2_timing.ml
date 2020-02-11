let time n f x =
  let t = Sys.time () in
  let res = f x in
  Printf.printf "[%s] ran in %fs\n" n (Sys.time() -. t);
  res

let output_bytes = Bytes.create 64
let output_bigstring = Bigstring.create 64

let rec repeat_bytes_test_from_bytes hash n (input: Bytes.t) =
  if n > 0 then begin
    hash Bytes.empty input output_bytes;
    repeat_bytes_test_from_bytes hash (n-1) output_bytes
  end

let rec repeat_bytes_test_from_bigstring hash n (input: Bigstring.t) =
  if n > 0 then begin
    let output = Bigstring.to_bytes output_bigstring in
    let input = Bigstring.to_bytes input in
    hash Bytes.empty input output;
    repeat_bytes_test_from_bigstring hash (n-1) (Bigstring.of_bytes input)
  end

let rec repeat_bigstring_test_from_bigstring hash n (input: Bigstring.t) =
  if n > 0 then begin
    hash Bigstring.empty input output_bigstring;
    repeat_bigstring_test_from_bigstring hash (n-1) output_bigstring
  end

let rec repeat_bigstring_test_from_bytes hash n (input: Bytes.t) =
  if n > 0 then begin
    let output = Bigstring.of_bytes output_bytes in
    let input = Bigstring.of_bytes input in
    hash Bigstring.empty input output;
    repeat_bigstring_test_from_bytes hash (n-1) (Bigstring.to_bytes input)
  end

let rec repeat_digestif_bytes_from_bytes n (input: Bytes.t) =
  if n > 0 then begin
    let output = Digestif.BLAKE2B.digest_bytes input in
    repeat_digestif_bytes_from_bytes (n-1) (Digestif.BLAKE2B.to_hex output)
  end

let rec repeat_digestif_bigstring_from_bigstring n (input: Bigstring.t) =
  if n > 0 then begin
    let output = Digestif.BLAKE2B.digest_bigstring input in
    repeat_digestif_bigstring_from_bigstring (n-1) (Bigstring.of_bytes (Digestif.BLAKE2B.to_hex output))
  end


let _ =

  let reps = 2000000 in

  time "Digestif.c Blake2b (bytes API from bytes)" (repeat_digestif_bytes_from_bytes reps) (Bytes.create 64);
  time "Hacl.Blake2b_256 (bytes API from bytes)" (repeat_bytes_test_from_bytes Hacl.blake2b_256_bytes reps) (Bytes.create 64);
  time "Hacl.Blake2b_32 (bytes API from bytes)" (repeat_bytes_test_from_bytes Hacl.blake2b_32_bytes reps) (Bytes.create 64);

  time "Hacl.Blake2b_256 (bytes API from bigstring)" (repeat_bytes_test_from_bigstring Hacl.blake2b_256_bytes reps) (Bigstring.create 64);
  time "Hacl.Blake2b_32 (bytes API from bigstring)" (repeat_bytes_test_from_bigstring Hacl.blake2b_32_bytes reps) (Bigstring.create 64);

  time "Digestif.c Blake2b (bigstring API from bigstring)" (repeat_digestif_bigstring_from_bigstring reps) (Bigstring.create 64);
  time "Hacl.Blake2b_256 (bigstring API from bigstring)" (repeat_bigstring_test_from_bigstring Hacl.Blake2b_256.hash reps) (Bigstring.create 64);
  time "Hacl.Blake2b_32 (bigstring API from bigstring)" (repeat_bigstring_test_from_bigstring Hacl.Blake2b_32.hash reps) (Bigstring.create 64);

  time "Hacl.Blake2b_256 (bigstring API from bytes)" (repeat_bigstring_test_from_bytes Hacl.Blake2b_256.hash reps) (Bytes.create 64);
  time "Hacl.Blake2b_32 (bigstring API from bytes)" (repeat_bigstring_test_from_bytes Hacl.Blake2b_32.hash reps) (Bytes.create 64)
