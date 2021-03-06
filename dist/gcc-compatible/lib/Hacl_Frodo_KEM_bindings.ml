open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Frodo_KEM_crypto_kem_keypair =
      foreign "Hacl_Frodo_KEM_crypto_kem_keypair"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning uint32_t)))
      
    let hacl_Frodo_KEM_crypto_kem_enc =
      foreign "Hacl_Frodo_KEM_crypto_kem_enc"
        (ocaml_bytes @->
           (ocaml_bytes @-> (ocaml_bytes @-> (returning uint32_t))))
      
    let hacl_Frodo_KEM_crypto_kem_dec =
      foreign "Hacl_Frodo_KEM_crypto_kem_dec"
        (ocaml_bytes @->
           (ocaml_bytes @-> (ocaml_bytes @-> (returning uint32_t))))
      
  end