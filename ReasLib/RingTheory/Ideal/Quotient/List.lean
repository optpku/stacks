/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Quotients by a List of Generators

This leaf packages the canonical comparison between quotienting first by the
head of a list and then by the mapped tail, and quotienting once by the whole
list.  It is independent of local, Noetherian, and regular-sequence
hypotheses.
-/

universe u v

namespace Ideal.Quotient.List

section Ring

variable {A : Type u} [CommRing A]

/-- Tag `02IE`: mapping the ideal of a cons list through the quotient by its
head leaves exactly the ideal of the mapped tail. -/
@[simp, stacks 02IE "mapped cons-list quotient ideal"]
theorem map_cons (r : A) (rs : List A) :
    Ideal.map (Ideal.Quotient.mk (Ideal.span ({r} : Set A))) (Ideal.ofList (r :: rs)) =
      Ideal.ofList (rs.map (Ideal.Quotient.mk (Ideal.span ({r} : Set A)))) := sorry

/-- Tag `02IE`: quotienting by a list may be performed by first quotienting
by its head and then by its mapped tail. -/
@[stacks 02IE "list head quotient comparison"]
noncomputable def consRingEquiv (r : A) (rs : List A) :
    ((A ⧸ Ideal.span ({r} : Set A)) ⧸
      Ideal.ofList (rs.map (Ideal.Quotient.mk (Ideal.span ({r} : Set A))))) ≃+*
      A ⧸ Ideal.ofList (r :: rs) :=
  (Ideal.quotEquivOfEq
      (Ideal.map_ofList (Ideal.Quotient.mk (Ideal.span ({r} : Set A))) rs).symm).trans
    ((DoubleQuot.quotQuotEquivQuotSup (Ideal.span ({r} : Set A)) (Ideal.ofList rs)).trans
      (Ideal.quotEquivOfEq (Ideal.ofList_cons r rs).symm))

/-- The list head-quotient comparison sends the double class of an element to
its class modulo the whole list ideal. -/
@[simp, stacks 02IE "list head quotient representative"]
theorem consRingEquiv_apply_mk_mk (r : A) (rs : List A) (x : A) :
    consRingEquiv r rs
      (Ideal.Quotient.mk
        (Ideal.ofList (rs.map (Ideal.Quotient.mk (Ideal.span ({r} : Set A)))))
        (Ideal.Quotient.mk (Ideal.span ({r} : Set A)) x)) =
      Ideal.Quotient.mk (Ideal.ofList (r :: rs)) x := sorry

/-- Mapping the ideal of an appended list through the quotient by its prefix
leaves exactly the ideal of the mapped suffix. -/
@[simp, stacks 02IE "mapped appended-list quotient ideal"]
theorem map_append (ys zs : List A) :
    Ideal.map (Ideal.Quotient.mk (Ideal.ofList ys)) (Ideal.ofList (ys ++ zs)) =
      Ideal.ofList (zs.map (Ideal.Quotient.mk (Ideal.ofList ys))) := sorry

/-- Tag `02IE`: quotienting by a list prefix and then by its mapped suffix is
canonically the same as quotienting once by the appended list. -/
@[stacks 02IE "appended-list quotient comparison"]
noncomputable def appendRingEquiv (ys zs : List A) :
    ((A ⧸ Ideal.ofList ys) ⧸
      Ideal.ofList (zs.map (Ideal.Quotient.mk (Ideal.ofList ys)))) ≃+*
      A ⧸ Ideal.ofList (ys ++ zs) :=
  (Ideal.quotEquivOfEq
      (Ideal.map_ofList (Ideal.Quotient.mk (Ideal.ofList ys)) zs).symm).trans
    ((DoubleQuot.quotQuotEquivQuotSup (Ideal.ofList ys) (Ideal.ofList zs)).trans
      (Ideal.quotEquivOfEq (Ideal.ofList_append ys zs).symm))

/-- The appended-list quotient comparison sends the double class of an
element to its class modulo the appended list ideal. -/
@[simp, stacks 02IE "appended-list quotient representative"]
theorem appendRingEquiv_apply_mk_mk (ys zs : List A) (x : A) :
    appendRingEquiv ys zs
      (Ideal.Quotient.mk
        (Ideal.ofList (zs.map (Ideal.Quotient.mk (Ideal.ofList ys))))
        (Ideal.Quotient.mk (Ideal.ofList ys) x)) =
      Ideal.Quotient.mk (Ideal.ofList (ys ++ zs)) x := sorry

end Ring

section Algebra

variable {R : Type u} {A : Type v} [CommSemiring R] [CommRing A] [Algebra R A]

/-- Tag `02IE`: the list head-quotient comparison is canonical as an
`R`-algebra equivalence. -/
@[stacks 02IE "algebra list head quotient comparison"]
noncomputable def consAlgEquiv (r : A) (rs : List A) :
    ((A ⧸ Ideal.span ({r} : Set A)) ⧸
      Ideal.ofList (rs.map (Ideal.Quotient.mk (Ideal.span ({r} : Set A))))) ≃ₐ[R]
      A ⧸ Ideal.ofList (r :: rs) :=
  (Ideal.quotientEquivAlgOfEq R
      (Ideal.map_ofList (Ideal.Quotient.mk (Ideal.span ({r} : Set A))) rs).symm).trans
    ((DoubleQuot.quotQuotEquivQuotSupₐ R (Ideal.span ({r} : Set A)) (Ideal.ofList rs)).trans
      (Ideal.quotientEquivAlgOfEq R (Ideal.ofList_cons r rs).symm))

/-- The algebra list head-quotient comparison sends the double class of an
element to its class modulo the whole list ideal. -/
@[simp, stacks 02IE "algebra list head quotient representative"]
theorem consAlgEquiv_apply_mk_mk (r : A) (rs : List A) (x : A) :
    consAlgEquiv (R := R) r rs
      (Ideal.Quotient.mk
        (Ideal.ofList (rs.map (Ideal.Quotient.mk (Ideal.span ({r} : Set A)))))
        (Ideal.Quotient.mk (Ideal.span ({r} : Set A)) x)) =
      Ideal.Quotient.mk (Ideal.ofList (r :: rs)) x := sorry

/-- Tag `02IE`: the appended-list quotient comparison is canonical as an
`R`-algebra equivalence. -/
@[stacks 02IE "algebra appended-list quotient comparison"]
noncomputable def appendAlgEquiv (ys zs : List A) :
    ((A ⧸ Ideal.ofList ys) ⧸
      Ideal.ofList (zs.map (Ideal.Quotient.mk (Ideal.ofList ys)))) ≃ₐ[R]
      A ⧸ Ideal.ofList (ys ++ zs) :=
  (Ideal.quotientEquivAlgOfEq R
      (Ideal.map_ofList (Ideal.Quotient.mk (Ideal.ofList ys)) zs).symm).trans
    ((DoubleQuot.quotQuotEquivQuotSupₐ R (Ideal.ofList ys) (Ideal.ofList zs)).trans
      (Ideal.quotientEquivAlgOfEq R (Ideal.ofList_append ys zs).symm))

/-- The algebra appended-list quotient comparison sends the double class of
an element to its class modulo the appended list ideal. -/
@[simp, stacks 02IE "algebra appended-list quotient representative"]
theorem appendAlgEquiv_apply_mk_mk (ys zs : List A) (x : A) :
    appendAlgEquiv (R := R) ys zs
      (Ideal.Quotient.mk
        (Ideal.ofList (zs.map (Ideal.Quotient.mk (Ideal.ofList ys))))
        (Ideal.Quotient.mk (Ideal.ofList ys) x)) =
      Ideal.Quotient.mk (Ideal.ofList (ys ++ zs)) x := sorry

end Algebra

end Ideal.Quotient.List
