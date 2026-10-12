/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Pseudofunctor
public import ReasLib.CategoryTheory.Fibered.Cleavage.Pseudofunctor.Comparison

/-!
# Comparing explicit and selected fiber pseudofunctors

This file is the application boundary between an arbitrary explicit cleavage and the cleavage
selected from a fibred projection. The comparison data remains owned by the neutral
change-of-cleavage API.
-/

@[expose] public section

universe vC vS uC uS

namespace CategoryTheory

open Bicategory Functor Opposite
open scoped CategoryTheory.Bicategory Pseudofunctor.StrongTrans

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S]

namespace Functor.Cleavage

variable {p : S ⥤ C}

/-- The fiber pseudofunctor for an explicit cleavage is canonically equivalent to the one
obtained from the selected cleavage of a fibred projection. -/
@[stacks 02XO "independence of the selected cleavage"]
noncomputable def toPseudofunctor.selectedEquivalence
    (chi : p.Cleavage) [p.IsFibered] :
    chi.toPseudofunctor ≌ fiberPseudofunctor p :=
  toPseudofunctor.uniqueEquivalence chi (Cleavage.ofIsFibered p)

/-- The forward transformation of the explicit-to-selected equivalence is the canonical
change-of-cleavage transformation. -/
@[simp]
theorem toPseudofunctor.selectedEquivalence.hom
    (chi : p.Cleavage) [p.IsFibered] :
    (toPseudofunctor.selectedEquivalence chi).hom =
      toPseudofunctor.uniqueStrongTrans chi (Cleavage.ofIsFibered p) := sorry

/-- The inverse transformation of the explicit-to-selected equivalence is the canonical
comparison back to the explicit cleavage. -/
@[simp]
theorem toPseudofunctor.selectedEquivalence.inv
    (chi : p.Cleavage) [p.IsFibered] :
    (toPseudofunctor.selectedEquivalence chi).inv =
      toPseudofunctor.uniqueStrongTrans (Cleavage.ofIsFibered p) chi := sorry

/-- The indexed presentation of the forward explicit-to-selected comparison is the canonical
change from the explicit cleavage to the selected cleavage. -/
@[simp]
theorem toPseudofunctor.selectedEquivalence.hom.toIndexedFunctor
    (chi : p.Cleavage) [p.IsFibered] :
    (toPseudofunctor.selectedEquivalence chi).hom.toIndexedFunctor =
      Indexed.comparison chi (Cleavage.ofIsFibered p) := sorry

/-- The indexed presentation of the inverse selected-to-explicit comparison is the canonical
change from the selected cleavage to the explicit cleavage. -/
@[simp]
theorem toPseudofunctor.selectedEquivalence.inv.toIndexedFunctor
    (chi : p.Cleavage) [p.IsFibered] :
    (toPseudofunctor.selectedEquivalence chi).inv.toIndexedFunctor =
      Indexed.comparison (Cleavage.ofIsFibered p) chi := sorry

/-- Components of the forward explicit-to-selected comparison are identity functors on the
standard fibers. -/
@[simp]
theorem toPseudofunctor.selectedEquivalence.hom.app
    (chi : p.Cleavage) [p.IsFibered] (a : LocallyDiscrete Cᵒᵖ) :
    (toPseudofunctor.selectedEquivalence chi).hom.app a =
      𝟙 (chi.toPseudofunctor.obj a) := sorry

/-- Components of the inverse selected-to-explicit comparison are identity functors on the
standard fibers. -/
@[simp]
theorem toPseudofunctor.selectedEquivalence.inv.app
    (chi : p.Cleavage) [p.IsFibered] (a : LocallyDiscrete Cᵒᵖ) :
    (toPseudofunctor.selectedEquivalence chi).inv.app a =
      𝟙 ((fiberPseudofunctor p).obj a) := sorry

/-- Objectwise forward naturality of the explicit-to-selected comparison is the canonical
comparison between the corresponding reindexing functors. -/
@[simp]
theorem toPseudofunctor.selectedEquivalence.forward.naturality.hom.app
    (chi : p.Cleavage) [p.IsFibered]
    {a b : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b)
    (x : Fiber p (unop a.as)) :
    ((toPseudofunctor.selectedEquivalence chi).hom.naturality f).hom.toNatTrans.app x =
      (Reindex.uniqueIsoApp chi (Cleavage.ofIsFibered p) f.as.unop x).hom := sorry

/-- Objectwise inverse naturality of the explicit-to-selected comparison is the inverse
canonical comparison between the corresponding reindexing functors. -/
@[simp]
theorem toPseudofunctor.selectedEquivalence.forward.naturality.inv.app
    (chi : p.Cleavage) [p.IsFibered]
    {a b : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b)
    (x : Fiber p (unop a.as)) :
    ((toPseudofunctor.selectedEquivalence chi).hom.naturality f).inv.toNatTrans.app x =
      (Reindex.uniqueIsoApp chi (Cleavage.ofIsFibered p) f.as.unop x).inv := sorry

/-- Objectwise forward naturality of the selected-to-explicit inverse comparison is the
canonical comparison back to the explicit cleavage. -/
@[simp]
theorem toPseudofunctor.selectedEquivalence.inverse.naturality.hom.app
    (chi : p.Cleavage) [p.IsFibered]
    {a b : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b)
    (x : Fiber p (unop a.as)) :
    ((toPseudofunctor.selectedEquivalence chi).inv.naturality f).hom.toNatTrans.app x =
      (Reindex.uniqueIsoApp (Cleavage.ofIsFibered p) chi f.as.unop x).hom := sorry

/-- Objectwise inverse naturality of the selected-to-explicit inverse comparison is the
inverse canonical comparison back to the explicit cleavage. -/
@[simp]
theorem toPseudofunctor.selectedEquivalence.inverse.naturality.inv.app
    (chi : p.Cleavage) [p.IsFibered]
    {a b : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b)
    (x : Fiber p (unop a.as)) :
    ((toPseudofunctor.selectedEquivalence chi).inv.naturality f).inv.toNatTrans.app x =
      (Reindex.uniqueIsoApp (Cleavage.ofIsFibered p) chi f.as.unop x).inv := sorry

/-- Selecting the already selected cleavage gives the identity pseudofunctor equivalence. -/
@[simp]
theorem toPseudofunctor.selectedEquivalence.self [p.IsFibered] :
    toPseudofunctor.selectedEquivalence (Cleavage.ofIsFibered p) =
      Bicategory.Equivalence.id (fiberPseudofunctor p) := sorry

end Functor.Cleavage

end CategoryTheory
