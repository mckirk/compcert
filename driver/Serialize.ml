type json = Yojson.Safe.t

(* Util *)
open BinNums
open Camlcoq

let fail_parse n j = failwith ("Can't parse " ^ n ^ " from " ^ Yojson.Safe.show j)
let explode s = List.init (String.length s) (String.get s)

let string_to_Z (s : string) : coq_Z =
  let i64 = Int64.of_string s in
  Z.of_sint64 i64

let string_to_positive (s : string) : positive =
  let i64 = Int64.of_string s in
  P.of_int64 i64

(* JSON combinators *)

let parse_tuple2 (f1 : json -> 'a) (f2 : json -> 'b) j : ('a * 'b) =
  match j with (`List (j1 :: j2 :: [])) -> (f1 j1, f2 j2) | _ -> fail_parse "tuple2" j
let parse_tuple3 f1 f2 f3 j =
  match j with (`List (j1 :: j2 :: j3 :: [])) -> (f1 j1, f2 j2, f3 j3) | _ -> fail_parse "tuple3" j
let parse_tuple4 f1 f2 f3 f4 j =
  match j with (`List (j1 :: j2 :: j3 :: j4 :: [])) -> (f1 j1, f2 j2, f3 j3, f4 j4) | _ -> fail_parse "tuple4" j

let parse_list (f: json -> 'b) (j: json) : 'b list =
  match j with (`List l) -> List.map f l  | _ -> fail_parse "list" j

let parse_assoc_key (k: string) (f: json -> 'b)  (j: json) : 'b =
  match j with (`Assoc al) -> f (List.assoc k al)  | _ -> fail_parse ("assoc key " ^ k) j

let parse_option (f: json -> 'b) j : 'b option =
  match j with (`Null) -> None | `List (j2 :: []) -> Some (f j2) | _ -> fail_parse "option" j

(* Ocaml types *)
let parse_unit j =
  match j with (`Null) -> () | _ -> fail_parse "unit" j

let parse_bool j : bool =
  match j with (`Bool b) -> b | _ -> fail_parse "bool" j

let parse_string j =
  match j with (`String s) -> explode s | _ -> fail_parse "string" j


(* Base types *)
open AST
open Cminor
open Integers

let parse_positive j : BinNums.positive =
  match j with (`Int i) -> P.of_int i  | _ -> fail_parse "positive" j

let parse_ident_str j : ident =
  match j with (`String s) -> intern_string s | _ -> fail_parse "ident_str" j

let parse_coq_Z j =
  match j with (`Int i) -> Z.of_sint i  | `Intlit s -> string_to_Z s | _ -> fail_parse "coq_Z" j
let parse_nat j =
  match j with (`Int i) -> Nat.of_int i  | _ -> fail_parse "nat" j

module type Wordmod = sig
  val wordsize : Datatypes.nat
  type int = coq_Z
  val repr : coq_Z -> int
end

let parse_word (module M : Wordmod) j =
  match j with `Int i -> M.repr (Z.of_sint i) | `Intlit s -> M.repr (string_to_Z s) | _ -> fail_parse ("word" ^ Z.to_string (BinInt.Z.of_nat M.wordsize)) j


let parse_Int_int = parse_word (module Integers.Int)
let parse_Int64_int = parse_word (module Integers.Int64)
let parse_Ptrofs_int = parse_word (module Integers.Ptrofs)
let parse_float32 j = fail_parse "float32" j
let parse_float j = fail_parse "float" j

(* Generated *)

let parse_comparison (j : json) : comparison =
  match j with
  | `String "Ceq" -> Ceq
  | `String "Cne" -> Cne
  | `String "Clt" -> Clt
  | `String "Cle" -> Cle
  | `String "Cgt" -> Cgt
  | `String "Cge" -> Cge
  | _ -> fail_parse "comparison" j

let parse_typ (j : json) : typ =
  match j with
  | `String "Tint" -> Tint
  | `String "Tfloat" -> Tfloat
  | `String "Tlong" -> Tlong
  | `String "Tsingle" -> Tsingle
  | `String "Tany32" -> Tany32
  | `String "Tany64" -> Tany64
  | _ -> fail_parse "typ" j

let parse_rettype (j : json) : rettype =
  match j with
  | `List ((`String "Tret") :: a0 :: []) -> Tret (parse_typ a0)
  | `List ((`String "Tint8signed") :: []) -> Tint8signed
  | `List ((`String "Tint8unsigned") :: []) -> Tint8unsigned
  | `List ((`String "Tint16signed") :: []) -> Tint16signed
  | `List ((`String "Tint16unsigned") :: []) -> Tint16unsigned
  | `List ((`String "Tvoid") :: []) -> Tvoid
  | _ -> fail_parse "rettype" j

let parse_calling_convention (j : json) : calling_convention =
  {cc_vararg = parse_assoc_key "cc_vararg" parse_bool j;
   cc_unproto = parse_assoc_key "cc_unproto" parse_bool j;
   cc_structret = parse_assoc_key "cc_structret" parse_bool j}

let parse_signature (j : json) : signature =
  {sig_args = parse_assoc_key "sig_args" (parse_list parse_typ) j;
   sig_res = parse_assoc_key "sig_res" parse_rettype j;
   sig_cc = parse_assoc_key "sig_cc" parse_calling_convention j}

let parse_memory_chunk (j : json) : memory_chunk =
  match j with
  | `String "Mint8signed" -> Mint8signed
  | `String "Mint8unsigned" -> Mint8unsigned
  | `String "Mint16signed" -> Mint16signed
  | `String "Mint16unsigned" -> Mint16unsigned
  | `String "Mint32" -> Mint32
  | `String "Mint64" -> Mint64
  | `String "Mfloat32" -> Mfloat32
  | `String "Mfloat64" -> Mfloat64
  | `String "Many32" -> Many32
  | `String "Many64" -> Many64
  | _ -> fail_parse "memory_chunk" j

let parse_init_data (j : json) : init_data =
  match j with
  | `List ((`String "Init_int8") :: a0 :: []) -> Init_int8 (parse_Int_int a0)
  | `List ((`String "Init_int16") :: a0 :: []) -> Init_int16 (parse_Int_int a0)
  | `List ((`String "Init_int32") :: a0 :: []) -> Init_int32 (parse_Int_int a0)
  | `List ((`String "Init_int64") :: a0 :: []) -> Init_int64 (parse_Int64_int a0)
  | `List ((`String "Init_float32") :: a0 :: []) -> Init_float32 (parse_float32 a0)
  | `List ((`String "Init_float64") :: a0 :: []) -> Init_float64 (parse_float a0)
  | `List ((`String "Init_space") :: a0 :: []) -> Init_space (parse_coq_Z a0)
  | `List ((`String "Init_addrof") :: a0 :: a1 :: []) -> Init_addrof (parse_ident_str a0, parse_Ptrofs_int a1)
  | _ -> fail_parse "init_data" j

let parse_globvar (parse_v : json -> 'v) (j : json) : 'v globvar =
  {gvar_info = parse_assoc_key "gvar_info" parse_v j;
   gvar_init = parse_assoc_key "gvar_init" (parse_list parse_init_data) j;
   gvar_readonly = parse_assoc_key "gvar_readonly" parse_bool j;
   gvar_volatile = parse_assoc_key "gvar_volatile" parse_bool j}

let parse_globdef (parse_f : json -> 'f) (parse_v : json -> 'v) (j : json) : ('f, 'v) globdef =
  match j with
  | `List ((`String "Gfun") :: a0 :: []) -> Gfun (parse_f a0)
  | `List ((`String "Gvar") :: a0 :: []) -> Gvar (parse_globvar parse_v a0)
  | _ -> fail_parse "globdef" j

let parse_AST_program (parse_f : json -> 'f) (parse_v : json -> 'v) (j : json) : ('f, 'v) AST.program =
  {prog_defs = parse_assoc_key "prog_defs" (parse_list (parse_tuple2 parse_ident_str (parse_globdef parse_f parse_v))) j;
   prog_public = parse_assoc_key "prog_public" (parse_list parse_ident_str) j;
   prog_main = parse_assoc_key "prog_main" parse_ident_str j}

let parse_external_function (j : json) : external_function =
  match j with
  | `List ((`String "EF_external") :: a0 :: a1 :: []) -> EF_external (parse_string a0, parse_signature a1)
  | `List ((`String "EF_builtin") :: a0 :: a1 :: []) -> EF_builtin (parse_string a0, parse_signature a1)
  | `List ((`String "EF_runtime") :: a0 :: a1 :: []) -> EF_runtime (parse_string a0, parse_signature a1)
  | `List ((`String "EF_vload") :: a0 :: []) -> EF_vload (parse_memory_chunk a0)
  | `List ((`String "EF_vstore") :: a0 :: []) -> EF_vstore (parse_memory_chunk a0)
  | `List ((`String "EF_malloc") :: []) -> EF_malloc
  | `List ((`String "EF_free") :: []) -> EF_free
  | `List ((`String "EF_memcpy") :: a0 :: a1 :: []) -> EF_memcpy (parse_coq_Z a0, parse_coq_Z a1)
  | `List ((`String "EF_annot") :: a0 :: a1 :: a2 :: []) -> EF_annot (parse_positive a0, parse_string a1, parse_list parse_typ a2)
  | `List ((`String "EF_annot_val") :: a0 :: a1 :: a2 :: []) -> EF_annot_val (parse_positive a0, parse_string a1, parse_typ a2)
  | `List ((`String "EF_inline_asm") :: a0 :: a1 :: a2 :: []) -> EF_inline_asm (parse_string a0, parse_signature a1, parse_list parse_string a2)
  | `List ((`String "EF_debug") :: a0 :: a1 :: a2 :: []) -> EF_debug (parse_positive a0, parse_ident_str a1, parse_list parse_typ a2)
  | _ -> fail_parse "external_function" j

let parse_AST_fundef (parse_f : json -> 'f) (j : json) : 'f AST.fundef =
  match j with
  | `List ((`String "Internal") :: a0 :: []) -> Internal (parse_f a0)
  | `List ((`String "External") :: a0 :: []) -> External (parse_external_function a0)
  | _ -> fail_parse "AST.fundef" j

let parse_constant (j : json) : constant =
  match j with
  | `List ((`String "Ointconst") :: a0 :: []) -> Ointconst (parse_Int_int a0)
  | `List ((`String "Ofloatconst") :: a0 :: []) -> Ofloatconst (parse_float a0)
  | `List ((`String "Osingleconst") :: a0 :: []) -> Osingleconst (parse_float32 a0)
  | `List ((`String "Olongconst") :: a0 :: []) -> Olongconst (parse_Int64_int a0)
  | `List ((`String "Oaddrsymbol") :: a0 :: a1 :: []) -> Oaddrsymbol (parse_ident_str a0, parse_Ptrofs_int a1)
  | `List ((`String "Oaddrstack") :: a0 :: []) -> Oaddrstack (parse_Ptrofs_int a0)
  | _ -> fail_parse "constant" j

let parse_unary_operation (j : json) : unary_operation =
  match j with
  | `String "Ocast8unsigned" -> Ocast8unsigned
  | `String "Ocast8signed" -> Ocast8signed
  | `String "Ocast16unsigned" -> Ocast16unsigned
  | `String "Ocast16signed" -> Ocast16signed
  | `String "Onegint" -> Onegint
  | `String "Onotint" -> Onotint
  | `String "Onegf" -> Onegf
  | `String "Oabsf" -> Oabsf
  | `String "Onegfs" -> Onegfs
  | `String "Oabsfs" -> Oabsfs
  | `String "Osingleoffloat" -> Osingleoffloat
  | `String "Ofloatofsingle" -> Ofloatofsingle
  | `String "Ointoffloat" -> Ointoffloat
  | `String "Ointuoffloat" -> Ointuoffloat
  | `String "Ofloatofint" -> Ofloatofint
  | `String "Ofloatofintu" -> Ofloatofintu
  | `String "Ointofsingle" -> Ointofsingle
  | `String "Ointuofsingle" -> Ointuofsingle
  | `String "Osingleofint" -> Osingleofint
  | `String "Osingleofintu" -> Osingleofintu
  | `String "Onegl" -> Onegl
  | `String "Onotl" -> Onotl
  | `String "Ointoflong" -> Ointoflong
  | `String "Olongofint" -> Olongofint
  | `String "Olongofintu" -> Olongofintu
  | `String "Olongoffloat" -> Olongoffloat
  | `String "Olonguoffloat" -> Olonguoffloat
  | `String "Ofloatoflong" -> Ofloatoflong
  | `String "Ofloatoflongu" -> Ofloatoflongu
  | `String "Olongofsingle" -> Olongofsingle
  | `String "Olonguofsingle" -> Olonguofsingle
  | `String "Osingleoflong" -> Osingleoflong
  | `String "Osingleoflongu" -> Osingleoflongu
  | _ -> fail_parse "unary_operation" j

let parse_binary_operation (j : json) : binary_operation =
  match j with
  | `List ((`String "Oadd") :: []) -> Oadd
  | `List ((`String "Osub") :: []) -> Osub
  | `List ((`String "Omul") :: []) -> Omul
  | `List ((`String "Odiv") :: []) -> Odiv
  | `List ((`String "Odivu") :: []) -> Odivu
  | `List ((`String "Omod") :: []) -> Omod
  | `List ((`String "Omodu") :: []) -> Omodu
  | `List ((`String "Oand") :: []) -> Oand
  | `List ((`String "Oor") :: []) -> Oor
  | `List ((`String "Oxor") :: []) -> Oxor
  | `List ((`String "Oshl") :: []) -> Oshl
  | `List ((`String "Oshr") :: []) -> Oshr
  | `List ((`String "Oshru") :: []) -> Oshru
  | `List ((`String "Oaddf") :: []) -> Oaddf
  | `List ((`String "Osubf") :: []) -> Osubf
  | `List ((`String "Omulf") :: []) -> Omulf
  | `List ((`String "Odivf") :: []) -> Odivf
  | `List ((`String "Oaddfs") :: []) -> Oaddfs
  | `List ((`String "Osubfs") :: []) -> Osubfs
  | `List ((`String "Omulfs") :: []) -> Omulfs
  | `List ((`String "Odivfs") :: []) -> Odivfs
  | `List ((`String "Oaddl") :: []) -> Oaddl
  | `List ((`String "Osubl") :: []) -> Osubl
  | `List ((`String "Omull") :: []) -> Omull
  | `List ((`String "Odivl") :: []) -> Odivl
  | `List ((`String "Odivlu") :: []) -> Odivlu
  | `List ((`String "Omodl") :: []) -> Omodl
  | `List ((`String "Omodlu") :: []) -> Omodlu
  | `List ((`String "Oandl") :: []) -> Oandl
  | `List ((`String "Oorl") :: []) -> Oorl
  | `List ((`String "Oxorl") :: []) -> Oxorl
  | `List ((`String "Oshll") :: []) -> Oshll
  | `List ((`String "Oshrl") :: []) -> Oshrl
  | `List ((`String "Oshrlu") :: []) -> Oshrlu
  | `List ((`String "Ocmp") :: a0 :: []) -> Ocmp (parse_comparison a0)
  | `List ((`String "Ocmpu") :: a0 :: []) -> Ocmpu (parse_comparison a0)
  | `List ((`String "Ocmpf") :: a0 :: []) -> Ocmpf (parse_comparison a0)
  | `List ((`String "Ocmpfs") :: a0 :: []) -> Ocmpfs (parse_comparison a0)
  | `List ((`String "Ocmpl") :: a0 :: []) -> Ocmpl (parse_comparison a0)
  | `List ((`String "Ocmplu") :: a0 :: []) -> Ocmplu (parse_comparison a0)
  | _ -> fail_parse "binary_operation" j

let rec parse_expr (j : json) : expr =
  match j with
  | `List ((`String "Evar") :: a0 :: []) -> Evar (parse_ident_str a0)
  | `List ((`String "Econst") :: a0 :: []) -> Econst (parse_constant a0)
  | `List ((`String "Eunop") :: a0 :: a1 :: []) -> Eunop (parse_unary_operation a0, parse_expr a1)
  | `List ((`String "Ebinop") :: a0 :: a1 :: a2 :: []) -> Ebinop (parse_binary_operation a0, parse_expr a1, parse_expr a2)
  | `List ((`String "Eload") :: a0 :: a1 :: []) -> Eload (parse_memory_chunk a0, parse_expr a1)
  | _ -> fail_parse "expr" j

let parse_label = parse_ident_str

let rec parse_stmt (j : json) : stmt =
  match j with
  | `List ((`String "Sskip") :: []) -> Sskip
  | `List ((`String "Sassign") :: a0 :: a1 :: []) -> Sassign (parse_ident_str a0, parse_expr a1)
  | `List ((`String "Sstore") :: a0 :: a1 :: a2 :: []) -> Sstore (parse_memory_chunk a0, parse_expr a1, parse_expr a2)
  | `List ((`String "Scall") :: a0 :: a1 :: a2 :: a3 :: []) -> Scall (parse_option parse_ident_str a0, parse_signature a1, parse_expr a2, parse_list parse_expr a3)
  | `List ((`String "Stailcall") :: a0 :: a1 :: a2 :: []) -> Stailcall (parse_signature a0, parse_expr a1, parse_list parse_expr a2)
  | `List ((`String "Sbuiltin") :: a0 :: a1 :: a2 :: []) -> Sbuiltin (parse_option parse_ident_str a0, parse_external_function a1, parse_list parse_expr a2)
  | `List ((`String "Sseq") :: a0 :: a1 :: []) -> Sseq (parse_stmt a0, parse_stmt a1)
  | `List ((`String "Sifthenelse") :: a0 :: a1 :: a2 :: []) -> Sifthenelse (parse_expr a0, parse_stmt a1, parse_stmt a2)
  | `List ((`String "Sloop") :: a0 :: []) -> Sloop (parse_stmt a0)
  | `List ((`String "Sblock") :: a0 :: []) -> Sblock (parse_stmt a0)
  | `List ((`String "Sexit") :: a0 :: []) -> Sexit (parse_nat a0)
  | `List ((`String "Sswitch") :: a0 :: a1 :: a2 :: a3 :: []) -> Sswitch (parse_bool a0, parse_expr a1, parse_list (parse_tuple2 parse_coq_Z parse_nat) a2, parse_nat a3)
  | `List ((`String "Sreturn") :: a0 :: []) -> Sreturn (parse_option parse_expr a0)
  | `List ((`String "Slabel") :: a0 :: a1 :: []) -> Slabel (parse_label a0, parse_stmt a1)
  | `List ((`String "Sgoto") :: a0 :: []) -> Sgoto (parse_label a0)
  | _ -> fail_parse "stmt" j

let parse_coq_function (j : json) : coq_function =
  {fn_sig = parse_assoc_key "fn_sig" parse_signature j;
   fn_params = parse_assoc_key "fn_params" (parse_list parse_ident_str) j;
   fn_vars = parse_assoc_key "fn_vars" (parse_list parse_ident_str) j;
   fn_stackspace = parse_assoc_key "fn_stackspace" parse_coq_Z j;
   fn_body = parse_assoc_key "fn_body" parse_stmt j}

let parse_fundef = parse_AST_fundef parse_coq_function

let parse_program = parse_AST_program parse_fundef parse_unit
