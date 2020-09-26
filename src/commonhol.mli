(* ========================================================================== *)
(* COMMON HOL API (HOL Zero)                                                  *)
(* - Interface for the Common HOL API version 0.5                             *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2011-2015                            *)
(* ========================================================================== *)


module type CommonHOL_sig = sig

  (* System parameters *)

  val hol_system : string
  val hol_version : string
  val commonhol_version : string

  (* Library *)

  exception HolFail of string * string
  val hol_fail : string * string -> 'a
  exception HolError of string * string
  val hol_error : string * string -> 'a
  val internal_error : string -> 'a
  exception LocalFail
  val check : ('a -> bool) -> 'a -> 'a

  val pair : 'a -> 'b -> 'a * 'b
  val fst : 'a * 'b -> 'a
  val snd : 'a * 'b -> 'b
  val switch : 'a * 'b -> 'b * 'a

  val length : 'a list -> int
  val cons : 'a -> 'a list -> 'a list
  val is_empty : 'a list -> bool
  val is_nonempty : 'a list -> bool
  val hd : 'a list -> 'a
  val tl : 'a list -> 'a list
  val hd_tl : 'a list -> 'a * 'a list
  val front : 'a list -> 'a list
  val last : 'a list -> 'a
  val front_last : 'a list -> 'a list * 'a
  val el0 : int -> 'a list -> 'a
  val el : int -> 'a list -> 'a
  val append : 'a list -> 'a list -> 'a list
  val flatten : 'a list list -> 'a list
  val rev : 'a list -> 'a list
  val zip : 'a list -> 'b list -> ('a * 'b) list
  val unzip : ('a * 'b) list -> 'a list * 'b list
  val cut : int -> 'a list -> 'a list * 'a list
  val up_to : int -> int -> int list

  val (<*) : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
  val curry : ('a * 'b -> 'c) -> 'a -> 'b -> 'c
  val uncurry : ('a -> 'b -> 'c) -> 'a * 'b -> 'c
  val funpow : int -> ('a -> 'a) -> 'a -> 'a
  val swap_arg : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c
  val dbl_arg : ('a -> 'a -> 'b) -> 'a -> 'b
  val id_fn : 'a -> 'a
  val con_fn : 'a -> 'b -> 'a

  val pair_apply : ('a -> 'b) * ('c -> 'd) -> 'a * 'c -> 'b * 'd
  val map : ('a -> 'b) -> 'a list -> 'b list
  val bimap : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
  val foldl : ('b -> 'a -> 'b) -> 'b -> 'a list -> 'b
  val foldr : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val foldl1 : ('a -> 'a -> 'a) -> 'a list -> 'a
  val foldr1 : ('a -> 'a -> 'a) -> 'a list -> 'a
  val unfoldl : ('a -> 'a * 'b) -> 'a -> 'a * 'b list
  val unfoldr : ('a -> 'b * 'a) -> 'a -> 'b list * 'a
  val unfoldl1 : ('a -> 'a * 'a) -> 'a -> 'a list
  val unfoldr1 : ('a -> 'a * 'a) -> 'a -> 'a list
  val unfold : ('a -> 'a * 'a) -> 'a -> 'a list

  val find : ('a -> bool) -> 'a list -> 'a
  val filter : ('a -> bool) -> 'a list -> 'a list
  val partition : ('a -> bool) -> 'a list -> 'a list * 'a list
  val exists : ('a -> bool) -> 'a list -> bool
  val forall : ('a -> bool) -> 'a list -> bool

  val assoc : 'a -> ('a * 'b) list -> 'b
  val inv_assoc : 'b -> ('a * 'b) list -> 'a
  val fst_map : ('a -> 'c) -> ('a * 'b) list -> ('c * 'b) list
  val snd_map : ('b -> 'c) -> ('a * 'b) list -> ('a * 'c) list
  val fst_filter : ('a -> bool) -> ('a * 'b) list -> ('a * 'b) list
  val snd_filter : ('b -> bool) -> ('a * 'b) list -> ('a * 'b) list

  val try_find : ('a -> 'b) -> 'a list -> 'b
  val try_filter : ('a -> 'b) -> 'a list -> 'b list
  val can : ('a -> 'b) -> 'a -> bool
  val cannot : ('a -> 'b) -> 'a -> bool
  val repeat : ('a -> 'a) -> 'a -> 'a

  val do_map : ('a -> unit) -> 'a list -> unit

  val setify : 'a list -> 'a list
  val mem : 'a -> 'a list -> bool
  val insert : 'a -> 'a list -> 'a list
  val union : 'a list -> 'a list -> 'a list
  val unions : 'a list list -> 'a list
  val intersect : 'a list -> 'a list -> 'a list
  val subtract : 'a list -> 'a list -> 'a list
  val subset : 'a list -> 'a list -> bool
  val disjoint : 'a list -> 'a list -> bool
  val set_eq : 'a list -> 'a list -> bool
  val no_dups : 'a list -> bool
  val setify' : ('a->'a->bool) -> 'a list -> 'a list
  val mem' : ('a->'a->bool) -> 'a -> 'a list -> bool
  val insert' : ('a->'a->bool) -> 'a -> 'a list -> 'a list
  val union' : ('a->'a->bool) -> 'a list -> 'a list -> 'a list
  val unions' : ('a->'a->bool) -> 'a list list -> 'a list
  val intersect' : ('a->'a->bool) -> 'a list -> 'a list -> 'a list
  val subtract' : ('a->'a->bool) -> 'a list -> 'a list -> 'a list
  val subset' : ('a->'a->bool) -> 'a list -> 'a list -> bool
  val disjoint' : ('a->'a->bool) -> 'a list -> 'a list -> bool
  val set_eq' : ('a->'a->bool) -> 'a list -> 'a list -> bool
  val no_dups' : ('a->'a->bool) -> 'a list -> bool

  val implode : string list -> string
  val explode : string -> string list
  val char_implode : char list -> string
  val char_explode : string -> char list
  val int_of_string : string -> int
  val string_of_int : int -> string
  val string_variant : string list -> string -> string
  val quote0 : string -> string
  val quote : string -> string

  val report : string -> unit
  val warn : string -> unit

  val merge : ('a->'a->bool) -> 'a list -> 'a list -> 'a list
  val mergesort : ('a->'a->bool) -> 'a list -> 'a list

  (* Type *)

  type hol_type = Type.hol_type

  val type_tyvars : hol_type -> hol_type list

  val type_inst : (hol_type * hol_type) list -> hol_type -> hol_type
  val type_match0 : (hol_type * hol_type) list
                         -> hol_type -> hol_type -> (hol_type * hol_type) list
  val type_match : hol_type -> hol_type -> (hol_type * hol_type) list

  val type_eq : hol_type -> hol_type -> bool
  val type_lt : hol_type -> hol_type -> bool

  (* Type syntax *)

  type destructed_type =
        Type_var of string
      | Type_comp of (string * hol_type list)
  val dest_type : hol_type -> destructed_type

  val mk_var_type : string -> hol_type
  val dest_var_type : hol_type -> string
  val is_var_type : hol_type -> bool

  val mk_comp_type : string * hol_type list -> hol_type
  val dest_comp_type : hol_type -> string * hol_type list
  val is_comp_type : hol_type -> bool

  val bool_ty : hol_type
  val ind_ty : hol_type
  val nat_ty : hol_type

  val a_ty : hol_type
  val b_ty : hol_type
  val c_ty : hol_type

  val mk_fun_type : hol_type * hol_type -> hol_type
  val list_mk_fun_type : hol_type list * hol_type -> hol_type
  val dest_fun_type : hol_type -> hol_type * hol_type
  val strip_fun_type : hol_type -> hol_type list * hol_type
  val is_fun_type : hol_type -> bool

  val mk_prod_type : hol_type * hol_type -> hol_type
  val list_mk_prod_type : hol_type list -> hol_type
  val dest_prod_type : hol_type -> hol_type * hol_type
  val strip_prod_type : hol_type -> hol_type list
  val is_prod_type : hol_type -> bool

  (* Term *)

  type term = Term.term

  val type_of : term -> hol_type
  val term_tyvars : term -> hol_type list
  val free_vars : term -> term list
  val list_free_vars : term list -> term list
  val var_free_in : term -> term -> bool
  val term_free_in : term -> term -> bool
  val all_vars : term -> term list
  val list_all_vars : term list -> term list
  val alpha_eq : term -> term -> bool
  val same_types : term -> term -> bool
  val term_union : term list -> term list -> term list
  val rename_bvar : string -> term -> term

  val genvar : hol_type -> term
  val variant : term list -> term -> term
  val list_variant : term list -> term list -> term list
  val cvariant : term list -> term -> term
  val list_cvariant : term list -> term list -> term list

  val tyvar_inst : (hol_type * hol_type) list -> term -> term
  val var_inst : (term * term) list -> term -> term
  val subst : (term * term) list -> term -> term
  val var_match : term -> term -> (term * term) list
  val term_match : term -> term ->
                               (term * term) list * (hol_type * hol_type) list
  val find_subterm : (term -> bool) -> term -> term

  val term_eq : term -> term -> bool
  val term_lt : term -> term -> bool

  (* Term syntax *)

  type destructed_term =
        Term_var of (string * hol_type)
      | Term_const of (string * hol_type)
      | Term_comb of (term * term)
      | Term_abs of (term * term)
  val dest_term : term -> destructed_term

  val mk_var : string * hol_type -> term
  val dest_var : term -> string * hol_type
  val var_name : term -> string
  val var_type : term -> hol_type
  val is_var : term -> bool

  val mk_const : string * hol_type -> term
  val mk_gconst : string -> term
  val mk_iconst : string * (hol_type * hol_type) list -> term
  val dest_const : term -> string * hol_type
  val const_name : term -> string
  val const_type : term -> hol_type
  val is_const : term -> bool

  val mk_comb : term * term -> term
  val list_mk_comb : term * term list -> term
  val dest_comb : term -> term * term
  val rator : term -> term
  val rand : term -> term
  val strip_comb : term -> term * term list
  val is_comb : term -> bool

  val mk_abs : term * term -> term
  val list_mk_abs : term list * term -> term
  val dest_abs : term -> term * term
  val bvar : term -> term
  val body : term -> term
  val strip_abs : term -> term list * term
  val is_abs : term -> bool

  val true_tm : term
  val false_tm : term

  val mk_bin : term * term * term -> term
  val dest_bin : term -> term * term * term
  val dest_cbin : string -> term -> term * term
  val is_bin : term -> bool
  val is_cbin : string -> term -> bool

  val mk_binder : term * term * term -> term
  val dest_binder : term -> term * term * term
  val dest_cbinder : string -> term -> term * term
  val is_binder : term -> bool
  val is_cbinder : string -> term -> bool

  val mk_eq : term * term -> term
  val dest_eq : term -> term * term
  val eq_lhs : term -> term
  val eq_rhs : term -> term
  val is_eq : term -> bool

  val mk_not : term -> term
  val dest_not : term -> term
  val is_not : term -> bool

  val mk_conj : term * term -> term
  val list_mk_conj : term list -> term
  val dest_conj : term -> term * term
  val strip_conj : term -> term list
  val flatstrip_conj : term -> term list
  val is_conj : term -> bool

  val mk_disj : term * term -> term
  val list_mk_disj : term list -> term
  val dest_disj : term -> term * term
  val strip_disj : term -> term list
  val flatstrip_disj : term -> term list
  val is_disj : term -> bool

  val mk_imp : term * term -> term
  val list_mk_imp : term list * term -> term
  val dest_imp : term -> term * term
  val strip_imp : term -> term list * term
  val is_imp : term -> bool

  val mk_forall : term * term -> term
  val list_mk_forall : term list * term -> term
  val dest_forall : term -> term * term
  val strip_forall : term -> term list * term
  val is_forall : term -> bool

  val mk_exists : term * term -> term
  val list_mk_exists : term list * term -> term
  val dest_exists : term -> term * term
  val strip_exists : term -> term list * term
  val is_exists : term -> bool

  val mk_uexists : term * term -> term
  val dest_uexists : term -> term * term
  val is_uexists : term -> bool

  val mk_select : term * term -> term
  val dest_select : term -> term * term
  val is_select : term -> bool

  val mk_cond : term * term * term -> term
  val dest_cond : term -> term * term * term
  val is_cond : term -> bool

  val mk_let : (term * term) list * term -> term
  val dest_let : term -> (term * term) list * term
  val is_let : term -> bool

  val mk_pair : term * term -> term
  val list_mk_pair : term list -> term
  val dest_pair : term -> term * term
  val strip_pair : term -> term list
  val flatstrip_pair : term -> term list
  val is_pair : term -> bool

  val mk_nat : int -> term
  val dest_nat : term -> int
  val is_nat : term -> bool

  (* Thm *)

  type thm = Thm.thm

  val dest_thm : thm -> term list * term
  val asms : thm -> term list
  val concl : thm -> term

  val thm_eq : thm -> thm -> bool
  val thm_alpha_eq : thm -> thm -> bool
  val thm_free_vars : thm -> term list

  (* Theory commands *)

  val new_tyconst : string * int -> hol_type
  val is_tyconst_name : string -> bool
  val get_tyconst_arity : string -> int
  val get_all_tyconsts : unit -> (string * int) list

  val new_const : string * hol_type -> term
  val is_const_name : string -> bool
  val get_const_gtype : string -> hol_type
  val get_all_consts : unit -> (string * hol_type) list

  val new_axiom : string * term -> thm
  val get_axiom : string -> thm
  val get_all_axioms : unit -> (string * thm) list

  val new_const_definition : term -> thm
  val get_const_definition : string -> thm
  val get_all_const_definitions : unit -> (string * thm) list

  val new_tyconst_definition : string * thm -> thm
  val get_tyconst_definition : string -> thm
  val get_tyconst_definition_info : string -> thm * thm
  val get_all_tyconst_definitions : unit -> (string * thm) list
  val get_all_tyconst_definition_info : unit -> (string * (thm * thm)) list

  val new_fun_definition : term -> thm
  val get_fun_definition : string -> thm
  val get_all_fun_definitions : unit -> (string * thm) list

  val new_const_specification : string list * thm -> thm
  val get_const_specification : string -> thm
  val get_const_specification_info : string -> (string list * thm) * thm
  val get_all_const_specifications : unit -> (string list * thm) list
  val get_all_const_specification_info :
                       unit -> ((string list * thm) * thm) list

  val new_type_bijections : string -> string * string -> thm * thm
  val get_type_bijections : string -> thm * thm
  val get_type_bijection_info : string -> (string * string) * (thm * thm)
  val get_all_type_bijections : unit -> (string * (thm * thm)) list
  val get_all_type_bijection_info :
                      unit -> (string * ((string * string) * (thm * thm))) list

  (* Inference rules *)

  val add_asm_rule : term -> thm -> thm
  val alpha_link_conv : term -> term -> thm
  val alpha_conv : term -> term -> thm
  val assume_rule : term -> thm
  val beta_conv : term -> thm
  val ccontr_rule : term -> thm -> thm
  val choose_rule : term * thm -> thm -> thm
  val conj_rule : thm -> thm -> thm
  val conjunct1_rule : thm -> thm
  val conjunct2_rule : thm -> thm
  val contr_rule : term -> thm -> thm
  val deduct_antisym_rule : thm -> thm -> thm
  val disch_rule : term -> thm -> thm
  val disj1_rule : thm -> term -> thm
  val disj2_rule : term -> thm -> thm
  val disj_cases_rule : thm -> thm -> thm -> thm
  val eq_imp_rule1 : thm -> thm
  val eq_imp_rule2 : thm -> thm
  val eq_mp_rule : thm -> thm -> thm
  val eqf_elim_rule : thm -> thm
  val eqf_intro_rule : thm -> thm
  val eqt_elim_rule : thm -> thm
  val eqt_intro_rule : thm -> thm
  val eta_conv : term -> thm
  val exists_rule : term * term -> thm -> thm
  val gen_rule : term -> thm -> thm
  val imp_antisym_rule : thm -> thm -> thm
  val imp_trans_rule : thm -> thm -> thm
  val inst_rule : (term * term) list -> thm -> thm
  val inst_type_rule : (hol_type * hol_type) list -> thm -> thm
  val mp_rule : thm -> thm -> thm
  val not_elim_rule : thm -> thm
  val not_intro_rule : thm -> thm
  val prove_asm_rule : thm -> thm -> thm
  val eq_refl_conv : term -> thm
  val select_rule : thm -> thm
  val spec_rule : term -> thm -> thm
  val subs_rule : thm list -> thm -> thm
  val subs_conv : thm list -> term -> thm
  val subst_rule : (term * thm) list -> term -> thm -> thm
  val subst_conv : (term * thm) list -> term -> term -> thm
  val eq_sym_rule : thm -> thm
  val eq_sym_conv : term -> thm
  val eq_trans_rule : thm -> thm -> thm
  val undisch_rule : thm -> thm

  val mk_abs_rule : term -> thm -> thm
  val mk_comb_rule : thm -> thm -> thm
  val mk_comb1_rule : thm -> term -> thm
  val mk_comb2_rule : term -> thm -> thm
  val mk_bin_rule : term -> thm -> thm -> thm
  val mk_bin1_rule : term -> thm -> term -> thm
  val mk_bin2_rule : term -> term -> thm -> thm
  val mk_eq_rule : thm -> thm -> thm
  val mk_eq1_rule : thm -> term -> thm
  val mk_eq2_rule : term -> thm -> thm
  val mk_pair_rule : thm -> thm -> thm
  val mk_pair1_rule : thm -> term -> thm
  val mk_pair2_rule : term -> thm -> thm
  val mk_not_rule : thm -> thm
  val mk_conj_rule : thm -> thm -> thm
  val mk_conj1_rule : thm -> term -> thm
  val mk_conj2_rule : term -> thm -> thm
  val mk_disj_rule : thm -> thm -> thm
  val mk_disj1_rule : thm -> term -> thm
  val mk_disj2_rule : term -> thm -> thm
  val mk_imp_rule : thm -> thm -> thm
  val mk_imp1_rule : thm -> term -> thm
  val mk_imp2_rule : term -> thm -> thm
  val mk_forall_rule : term -> thm -> thm
  val mk_exists_rule : term -> thm -> thm
  val mk_uexists_rule : term -> thm -> thm
  val mk_select_rule : term -> thm -> thm

  val eval_suc_conv : term -> thm
  val eval_pre_conv : term -> thm
  val eval_add_conv : term -> thm
  val eval_sub_conv : term -> thm
  val eval_mult_conv : term -> thm
  val eval_exp_conv : term -> thm
  val eval_nat_eq_conv : term -> thm
  val eval_lt_conv : term -> thm
  val eval_le_conv : term -> thm
  val eval_gt_conv : term -> thm
  val eval_ge_conv : term -> thm
  val eval_even_conv : term -> thm
  val eval_odd_conv : term -> thm

  (* Theorems *)

  val true_def : thm
  val false_def : thm
  val not_def : thm
  val conj_def : thm
  val disj_def : thm
  val imp_alt_def_thm : thm
  val forall_def : thm
  val exists_def : thm
  val uexists_def : thm
  val one_one_def : thm
  val onto_def : thm
  val type_definition_def : thm
  val cond_def : thm
  val eta_ax : thm
  val imp_antisym_ax : thm
  val bool_cases_thm : thm
  val select_ax : thm
  val truth_thm : thm
  val not_true_thm : thm
  val excluded_middle_thm : thm

  val fst_def : thm
  val snd_def : thm
  val pair_eq_thm : thm
  val pair_surjective_thm : thm
  val fst_thm : thm
  val snd_thm : thm

  val infinity_ax : thm
  val ind_suc_not_zero_thm : thm
  val ind_suc_injective_thm : thm

  val suc_not_zero_thm : thm
  val suc_injective_thm : thm
  val nat_cases_thm : thm
  val nat_induction_thm : thm
  val nat_recursion_thm : thm
  val pre_def : thm
  val add_def : thm
  val sub_def : thm
  val mult_def : thm
  val exp_def : thm
  val lt_def : thm
  val le_def : thm
  val gt_def : thm
  val ge_def : thm
  val even_def : thm
  val odd_def : thm

  (* Fixity *)

  type assochand =
      LeftAssoc
    | RightAssoc
    | NonAssoc
  type fixity =
      Nonfix
    | Prefix
    | Infix of (int * assochand)
    | Postfix
    | Binder

  val set_type_fixity : string * fixity -> unit
  val get_type_fixity : string -> fixity
  val get_all_type_fixities : unit -> (string * fixity) list

  val set_fixity : string * fixity -> unit
  val get_fixity : string -> fixity
  val get_all_fixities : unit -> (string * fixity) list

  (* Parsing and pretty printing *)

  val parse_type : string -> hol_type
  val parse_term : string -> term

  val print_type : hol_type -> unit
  val print_term : term -> unit

  val print_qtype : hol_type -> unit
  val print_qterm : term -> unit
  val print_thm : thm -> unit

end;;
