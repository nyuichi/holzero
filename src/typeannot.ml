(* ========================================================================== *)
(* TYPE ANNOTATION (HOL Zero)                                                 *)
(* - Type annotation of preterms                                              *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2016                            *)
(* ========================================================================== *)


module TypeAnnot : TypeAnnot_sig = struct


(* This module defines two type annotation routines for preterms, used when   *)
(* printing term quotations.  The first gives a very verbose level of type    *)
(* annotation, whilst the second annotates at a minimal level.  The type      *)
(* annotation routine used depends on the type annotation mode setting.       *)

(* Note that although this module is used in the implementation of the pretty *)
(* printer, it is not a trusted component of the system.  This is because     *)
(* a (trusted) check is performed on the results of these routines before     *)
(* they are used.  This check is implemented in the 'TypeAnal' module.        *)


open Term;;
open Utils1;;

open Preterm;;
open TypeAnal;;



(* ** EXTRA PRETERM UTILITIES ** *)


(* domain_restrict *)

let domain_restrict xs xys =
  let test (x,y) = mem x xs in
  filter test xys;;


(* preterm_var *)

let rec preterm_var ptm =
  match ptm with
    Ptmvar _          -> ptm
  | Ptmtyped (ptm0,_) -> preterm_var ptm0
  | _                 -> hol_fail ("preterm_var","?");;


(* Notions of equivalence between varaibles *)

let var_equiv1 v1 v2 = (atom_preterm_name v1 = atom_preterm_name v2);;

let var_equiv2 theta v1 v2 = (preterm_inst theta v1 = preterm_inst theta v2);;


(* Pretype complexity of atoms *)

let atom_type_complexity ptm =
  match ptm with
    Ptmvar (_,pty) | Ptmconst (_,pty)
       -> pretype_complexity pty
  | _  -> hol_fail ("atom_type_complexity","?");;

let sort_by_type_complexity ptms =
  let nptms = map (fun ptm -> (atom_type_complexity ptm, ptm)) ptms in
  let nptms' = mergesort (fun (n1,ptm1) (n2,ptm2) -> (n1 < n2)) nptms in
  map snd nptms';;


(* Unresolved atoms *)

(* The "unresolved" atoms in a preterm are those involving generated tyvars.  *)

let unresolved_atoms atms = filter preterm_has_gtyvars atms;;

let ordered_unresolved_atoms atms =
  sort_by_type_complexity (unresolved_atoms atms);;



(* ** FULL TYPE ANNOTATION ** *)

(* This facility gets used during printing if the type annotation mode is set *)
(* to 'Full'.  It gives a type annotation to every occurrence of every        *)
(* variable and every occurrence of every polymorphic constant in the         *)
(* supplied preterm.  Note that non-polymorphic constants are not type        *)
(* annotated.                                                                 *)

(* If flag 'fl' is set, then conditional, pair and let-expressions are        *)
(* treated specially in that their associated "COND", "PAIR" and "LET"        *)
(* polymorphic constants are not type-annotated.  This enables them to be     *)
(* printed in their own special syntax when the language level mode is Full.  *)
(* Note that missing out such type annotations never reduces the overall      *)
(* amount of type information conveyed.                                       *)


(* Full annotation *)

let rec full_annotate_preterm fl ptm =
  match ptm with
    Ptmvar (_,pty)
       -> Ptmtyped (ptm,pty)         (* occurrence of a variable *)
  | Ptmconst (x,pty)
       -> if ((is_nonempty <* type_tyvars <* get_const_gtype) x)
            then Ptmtyped (ptm,pty)  (* occurrence of a polymorphic const *)
            else ptm                 (* occurrence of a non-polymorphic const *)
  | Ptmcomb (ptm1,ptm2)
       -> if fl && (is_cond_preterm ptm)
            then (* Conditional expression *)
                 let (ptm1,ptm2,ptm3) = dest_cond_preterm ptm in
                 let ptm1' = full_annotate_preterm fl ptm1 in
                 let ptm2' = full_annotate_preterm fl ptm2 in
                 let ptm3' = full_annotate_preterm fl ptm3 in
                 mk_cond_preterm (ptm1',ptm2',ptm3')
          else if fl && (is_pair_preterm ptm)
            then (* Pair expression *)
                 let ptms = strip_pair_preterm ptm in
                 let ptms' = map (full_annotate_preterm fl) ptms in
                 list_mk_pair_preterm ptms'
          else if fl && (is_let_preterm ptm)
            then (* Let-expression *)
                 let (vptms,ptm0) = dest_let_preterm ptm in
                 let vptms' = map (fun (v,ptm)-> (full_annotate_preterm fl v,
                                                  full_annotate_preterm fl ptm))
                                  vptms in
                 let ptm0' = full_annotate_preterm fl ptm0 in
                 mk_let_preterm (vptms',ptm0')
            else let ptm1' = full_annotate_preterm fl ptm1 in
                 let ptm2' = full_annotate_preterm fl ptm2 in
                 Ptmcomb (ptm1',ptm2')
  | Ptmabs (ptm1,ptm2)
       -> let ptm1' = full_annotate_preterm fl ptm1 in
          let ptm2' = full_annotate_preterm fl ptm2 in
          Ptmabs (ptm1',ptm2')
  | Ptmtyped (ptm0,pty)
       -> (match ptm0 with
             Ptmvar _ | Ptmconst _
               -> ptm                      (* don't double-annotate atoms *)
           | _ -> let ptm0' = full_annotate_preterm fl ptm0 in
                  Ptmtyped (ptm0',pty));;  (* keep existing annotations   *)



(* ** MINIMAL TYPE ANNOTATION ** *)

(* This facility gets used during printing if the type annotation mode is set *)
(* to 'Minimal'.  It takes a preterm and annotates a minimal selection of its *)
(* atoms sufficiently for the resulting printed output to not have any        *)
(* ambiguity about its types.  The particular atoms annotated are chosen in a *)
(* way that attempts to maximise the overall readability of the printed       *)
(* output.                                                                    *)

(* At the start of the algorithm, the types of all atoms in the supplied      *)
(* preterm are replaced with generated tyvars unique to each atom (in a       *)
(* process called "detyping"), and these generated tyvars then stay fixed in  *)
(* the preterm until its type-annotated result is passed up to the printer.   *)
(* Within the algorithm, the generated tyvars serve the dual purposes of a    *)
(* basis for calculating types and a label for pinpointing atoms.             *)


(* Atom sifting *)

(* This function sifts through its ordered input list of atoms (representing  *)
(* candidates for annotation, in order of preference), removing those atoms   *)
(* whose annotation would be unnecessary due to their generated tyvars being  *)
(* covered by other, preferable atoms.  Note that, unlike in other parts of   *)
(* the minimal type annotation implementation, the atoms in this routine are  *)
(* actually partially-type-instantiated atoms, with partially-resolved        *)
(* pretypes that reflect type information deduced from context.               *)

(* The sifting works by traversing the atom list input twice.  The first      *)
(* traversal removes any list items that only contain generated tyvars        *)
(* covered by earlier list items, and outputs the remaining items in reversed *)
(* order.  The second traversal does the same on the result of the first      *)
(* traversal, but in the opposite direction wrt the original input list       *)
(* ordering, thus removing earlier original list items that are subsumed by   *)
(* later ones.                                                                *)

let rec sift_atoms0 (atms0,gtys0) atms =
  match atms with
    atm1::atms2
       -> let gtys1 = preterm_gtyvars atm1 in
          let gtys2 = subtract gtys1 gtys0 in
          if (is_empty gtys2)
            then sift_atoms0 (atms0,gtys0) atms2
            else let atms0' = atm1::atms0 in
                 let gtys0' = gtys2 @ gtys0 in
                 sift_atoms0 (atms0',gtys0') atms2
  | [] -> atms0;;

let sift_atoms gtys0 atms =
  let atms1 = sift_atoms0 ([],gtys0) atms in     (* Traversal 1 *)
  let atms2 = sift_atoms0 ([],gtys0) atms1 in    (* Traversal 2 *)
  atms2;;


(* Closure information *)

(* This function is used in 'atom_info' to help work out what happens at the  *)
(* closure of a given var 'v'.  The complete generated-tyvar instn list       *)
(* 'thetaC' is used to determine whether 'v' is locally overloaded.  If it    *)
(* is, then a sufficient subset of overloaded var atoms with locally          *)
(* unresolved pretypes are earmarked for annotation.  If it isn't overloaded, *)
(* then all var atoms with 'v's name must unify.                              *)

(* The following inputs are taken:                                            *)
(*   thetaC  - Complete generated-tyvar instn list (using original term)      *)
(*   theta0  - Local generated-tyvar instn list (closed)                      *)
(*   fvs     - All local var atoms free at the closure point                  *)
(*   v       - The var being closed                                           *)
(* The following outputs are returned:                                        *)
(*   ovs     - Local var atoms overloaded with 'v' & thus due for annotation  *)
(*   vs2     - All local occurrences of 'v'                                   *)
(*   theta0' - Updated 'theta0', taking 'v's closure into account             *)

let closure_info (thetaC,theta0) fvs v =
  let vs1 = filter (var_equiv1 v) fvs in   (* var atoms with same name as 'v' *)
  let vs2 = filter (var_equiv2 thetaC v) vs1 in         (* occurrences of 'v' *)
  if (length vs2 < length vs1)
    then (* 'v' is overloaded *)
         let vtheta = map (fun v -> (v, preterm_inst theta0 v)) vs1 in
         let vs' = ordered_unresolved_atoms (map snd vtheta) in
         let vs'' = sift_atoms [] vs' in        (* pick sufficient subset *)
         let ovs = map (fun v' -> inv_assoc v' vtheta) vs'' in
         let gtys = map (snd <* dest_var_preterm) ovs in
         let theta1 = domain_restrict gtys thetaC in
         let theta0' = theta_closure theta0 theta1 in
         (ovs, vs2, theta0')
    else (* 'v' not overloaded *)
         let ptys = map (snd <* dest_var_preterm) vs1 in
         let theta0' = unify_pretype_list theta0 ptys in
         ([], vs2, theta0');;


(* Atom information *)

(* This bottom-up recursive function collects together various information    *)
(* deduced about atoms in the supplied preterm.  This is used by              *)
(* 'pick_atom_coverage' to decide which atoms to type-annotate.  Note that    *)
(* all atoms in the input and all atoms returned in the output retain their   *)
(* original detyped pretypes (because these ultimately get used to pinpoint   *)
(* individual atoms in the preterm).                                          *)

(* The following inputs are taken:                                            *)
(*   thetaC - Complete generated-tyvar instn list (using original term)       *)
(*   ptm    - The subterm under consideration                                 *)
(* The following outputs are returned:                                        *)
(*   ovs    - Local overloaded var atoms due for type annotation              *)
(*   fvs    - All var atoms free at the subterm level                         *)
(*   bvs    - All var atoms bound at the subterm level                        *)
(*   pcs    - All polymorphic const atoms in the subterm                      *)
(*   pty'   - Locally-resolved type of the subterm                            *)
(*   theta  - Instn list for generated tyvars, deduced from subterm           *)

let rec atom_info0 thetaC ptm =
  match ptm with
    Ptmvar (x,pty)
       -> ([],[ptm],[],[],pty,[])
  | Ptmconst (x,pty)
       -> if (pretype_has_gtyvars pty)
            then ([],[],[],[ptm],pty,[])     (* polymorphic const     *)
            else ([],[],[],[],pty,[])        (* non-polymorphic const *)
  | Ptmcomb (ptm1,ptm2)
       -> let (ovs1,fvs1,bvs1,pcs1,pty1,theta1) = atom_info0 thetaC ptm1 in
          let (ovs2,fvs2,bvs2,pcs2,pty2,theta2) = atom_info0 thetaC ptm2 in
          let ovs = ovs1 @ ovs2 in
          let fvs = fvs1 @ fvs2 in
          let bvs = bvs1 @ bvs2 in
          let pcs = union pcs1 pcs2 in
          let theta12 = theta1 @ theta2 in
          let (ptya,ptyb) = try  dest_fun_pretype pty1
               with HolFail _ ->  (pty2, new_pretype_gvar ()) in
          let ptyab = mk_fun_pretype (ptya,ptyb) in
          let theta = unify_pretype_pairs theta12 [(ptyab,pty1);(ptya,pty2)] in
          let ptyb' = pretype_inst theta ptyb in
          (ovs,fvs,bvs,pcs,ptyb',theta)
  | Ptmabs (ptmv,ptm0)
       -> let v = preterm_var ptmv in
          let ptyv = (snd <* dest_var_preterm) v in
          let (ovs0,fvs0,bvs0,pcs0,pty0,theta0) = atom_info0 thetaC ptm0 in
          let fvs00 = v::fvs0 in
          let (ovs1,bvs1,theta) = closure_info (thetaC,theta0) fvs00 v in
          let ovs = union ovs0 ovs1 in
          let fvs = subtract fvs00 bvs1 in
          let bvs = bvs1 @ bvs0 in
          let pty12 = mk_fun_pretype (ptyv,pty0) in
          let pty' = pretype_inst theta pty12 in
          (ovs,fvs,bvs,pcs0,pty',theta)
  | Ptmtyped (ptm0,pty)
       -> let (ovs0,fvs0,bvs0,pcs0,pty0,theta0) = atom_info0 thetaC ptm0 in
          let theta = unify_pretypes0 theta0 (pty0,pty) in
          let pty' = pretype_inst theta pty0 in
          (ovs0,fvs0,bvs0,pcs0,pty',theta);;

let atom_info thetaC ptm =
  let (ovs0,fvs0,bvs0,pcs0,_,theta0) = atom_info0 thetaC ptm in
  let fvs00 = setify' (var_equiv2 thetaC) fvs0 in
  let foo (ovs0,theta0) fv0 =
     let (ovs0',_,theta0') = closure_info (thetaC,theta0) fvs0 fv0 in
     let ovs0'' = union ovs0 ovs0' in
     (ovs0'',theta0') in
  let (ovs1,theta) = foldl foo (ovs0,theta0) fvs00 in
  let bvs1 = subtract bvs0 ovs0 in
  let fvs1 = subtract fvs0 ovs1 in
  (ovs1,fvs1,bvs1,pcs0,theta);;


(* Picking atoms for annotation *)

(* This chooses, from all the atoms in the supplied preterm, a subset that is *)
(* sufficient to be type-annotated so that the printed term can be read       *)
(* without type-ambiguity.  The subset is chosen according to a heuristic,    *)
(* with the aim of making the printed output as readable as possible.  Note   *)
(* that atoms are uniquely identified by their pretypes, because at this      *)
(* stage they still retain all the generated tyvars that come from detyping.  *)

(* Firstly 'atom_info' is called to collect together various information      *)
(* about the preterm, including a list of overloaded var atoms already        *)
(* earmarked for annotation ('ovs'), the free var atoms ('fvs'), the bound    *)
(* var atoms ('bvs'), the polymorphic const atoms ('pcs') and an intermediate *)
(* instn list for generated tyvars (deduced from the unannotated preterm and  *)
(* its overloaded var atoms).  These atoms all have their original "detyped"  *)
(* pretypes.  Type instantiations of all these atoms, wrt the intermediate    *)
(* instn list, are then worked out, and any resulting partially-type-         *)
(* instantiated atoms that no longer involve generated tyvars or that have    *)
(* become duplicates are ruled out.  The remaining partially-type-            *)
(* instantiated atoms, ordered wrt priority to be annotated, are passed to    *)
(* 'sift_atoms' as candidates for type annotation, which selects a subset     *)
(* based on minimising redundant type information.  An original detyped atom  *)
(* for each of these selected type-instantiated atoms is then worked out, and *)
(* these are joined with the already earmarked overloaded var atoms and       *)
(* passed as the output.                                                      *)

(* Note - Bound variables keep their order from 'atom_info' because,          *)
(* according to the heuristic, outermost bound vars have priority, regardless *)
(* of their type complexity.                                                  *)

let pick_atom_coverage thetaC pty_ ptm =
  let ptm1 = match pty_ with Some pty -> Ptmtyped (ptm,pty)
                           | None     -> ptm in
  let (ovs,fvs,bvs,pcs,theta) = atom_info thetaC ptm1 in
  let atom_theta atms = map (fun atm -> (atm, preterm_inst theta atm)) atms in
  let ovtheta = atom_theta ovs in
  let fvtheta = atom_theta fvs in
  let bvtheta = atom_theta bvs in
  let pctheta = atom_theta pcs in
  let fvs' = ordered_unresolved_atoms (map snd fvtheta) in
  let bvs' = unresolved_atoms (map snd bvtheta) in    (* See Note above *)
  let pcs' = ordered_unresolved_atoms (map snd pctheta) in
  let gtys0 = unions (map (preterm_gtyvars <* snd) ovtheta) in
  let atms' = sift_atoms gtys0 (bvs' @ fvs' @ pcs') in
  let atmtheta = bvtheta @ fvtheta @ pctheta in
  let atms = map (fun atm -> inv_assoc atm atmtheta) atms' in
  ovs @ atms;;


(* Annotating preterm atoms *)

(* This function transforms preterm 'ptm' by adding type annotations for      *)
(* atoms from 'atms' with types looked up from instn list 'thetaC'.  Note     *)
(* that the preterm will already have been detyped, and that the resulting    *)
(* generated tyvars remain in the preterm until now, and so each atom in the  *)
(* atom list uniquely identifies a specific atom within the preterm.  The     *)
(* resulting type-annotated preterm also has its original generated tyvars    *)
(* from detyping, but the added type annotations on atoms give all the        *)
(* information required to remove ambiguity in the printed quotation.         *)

let rec annotate_preterm_atoms thetaC atms ptm =
  match ptm with
    Ptmvar (x,pty) | Ptmconst (x,pty)
       -> if (mem ptm atms)
            then let pty' = pretype_inst thetaC pty in
                 Ptmtyped (ptm,pty')
            else ptm
  | Ptmcomb (ptm1,ptm2)
       -> let ptm1' = annotate_preterm_atoms thetaC atms ptm1 in
          let ptm2' = annotate_preterm_atoms thetaC atms ptm2 in
          if (ptm1' == ptm1) && (ptm2' == ptm2)
            then ptm
            else Ptmcomb (ptm1',ptm2')
  | Ptmabs (ptm1,ptm2)
       -> let ptm1' = annotate_preterm_atoms thetaC atms ptm1 in
          let ptm2' = annotate_preterm_atoms thetaC atms ptm2 in
          if (ptm1' == ptm1) && (ptm2' == ptm2)
            then ptm
            else Ptmabs (ptm1',ptm2')
  | Ptmtyped (ptm0,pty)
       -> let ptm0' = annotate_preterm_atoms thetaC atms ptm0 in
          if (ptm0' == ptm0)
            then ptm
            else Ptmtyped (ptm0',pty);;


(* Type annotation *)

(* This is the top-level minimal type annotation function.  It works by first *)
(* replacing types in atoms in the supplied preterm with generated tyvars.  A *)
(* complete instn list (called 'thetaC') for these generated tyvars to actual *)
(* types in the original term is then calculated.  This is then used to help  *)
(* pick a set of atoms to be type-annotated that is sufficient for the        *)
(* preterm to be read unambiguously, chosen with the intent of minimising     *)
(* annotation whilst maximising readability.  Finally, a labelling routine is *)
(* applied that annotates the chosen atoms according to 'thetaC'.             *)

(* The pretype option argument 'pty_' is set when the type of the top-level   *)
(* term is determined by the printing context (e.g. whilst printing theorem   *)
(* assumptions and conclusion).  When set, this can reduce the amount of      *)
(* annotation required to remove type ambiguity.                              *)

let min_annotate_preterm pty_ ptm =
  let ptm1 = detype_preterm ptm in
  let thetaC = preterm_pretype_match (ptm1,ptm) in
  let atms = pick_atom_coverage thetaC pty_ ptm1 in
  let ptm2 = annotate_preterm_atoms thetaC atms ptm1 in
  ptm2;;


end;;
