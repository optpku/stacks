/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Cleavage.Pseudofunctor.Comparison.Basic

/-!
# Coherence of change-of-cleavage pseudofunctor comparisons

The canonical comparisons between fiber pseudofunctors are compatible with identity,
composition, and reversal of cleavages. Direct component formulas keep downstream arguments
at the reindexing level.
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

/-- Comparing a cleavage with itself gives the identity strong transformation. -/
@[simp]
theorem toPseudofunctor.uniqueStrongTrans.self
    (chi : p.Cleavage) :
    toPseudofunctor.uniqueStrongTrans chi chi =
      Pseudofunctor.StrongTrans.id chi.toPseudofunctor := sorry

/-- Canonical change-of-cleavage strong transformations compose transitively. -/
@[simp]
theorem toPseudofunctor.uniqueStrongTrans.vcomp
    (chi₁ chi₂ chi₃ : p.Cleavage) :
    Pseudofunctor.StrongTrans.vcomp
        (toPseudofunctor.uniqueStrongTrans chi₁ chi₂)
        (toPseudofunctor.uniqueStrongTrans chi₂ chi₃) =
      toPseudofunctor.uniqueStrongTrans chi₁ chi₃ := sorry

/-- The inverse transformation in the canonical change-of-cleavage equivalence is the
canonical comparison in the reverse direction. -/
@[simp]
theorem toPseudofunctor.uniqueEquivalence.inv
    (chi₁ chi₂ : p.Cleavage) :
    (toPseudofunctor.uniqueEquivalence chi₁ chi₂).inv =
      toPseudofunctor.uniqueStrongTrans chi₂ chi₁ := sorry

/-- The indexed presentation of the inverse canonical pseudofunctor equivalence is the reverse
change-of-cleavage comparison. -/
@[simp]
theorem toPseudofunctor.uniqueEquivalence.inv.toIndexedFunctor
    (chi₁ chi₂ : p.Cleavage) :
    (toPseudofunctor.uniqueEquivalence chi₁ chi₂).inv.toIndexedFunctor =
      Indexed.comparison chi₂ chi₁ := sorry

/-- The forward component of the canonical change-of-cleavage equivalence is the identity
functor on the common fiber. -/
@[simp]
theorem toPseudofunctor.uniqueEquivalence.hom.app
    (chi₁ chi₂ : p.Cleavage) (a : LocallyDiscrete Cᵒᵖ) :
    (toPseudofunctor.uniqueEquivalence chi₁ chi₂).hom.app a =
      𝟙 (chi₁.toPseudofunctor.obj a) := sorry

/-- The inverse component of the canonical change-of-cleavage equivalence is the identity
functor on the common fiber. -/
@[simp]
theorem toPseudofunctor.uniqueEquivalence.inv.app
    (chi₁ chi₂ : p.Cleavage) (a : LocallyDiscrete Cᵒᵖ) :
    (toPseudofunctor.uniqueEquivalence chi₁ chi₂).inv.app a =
      𝟙 (chi₂.toPseudofunctor.obj a) := sorry

/-- Objectwise, forward naturality of the canonical pseudofunctor equivalence is the
canonical reindexing comparison. -/
@[simp]
theorem toPseudofunctor.uniqueEquivalence.forward.naturality.hom.app
    (chi₁ chi₂ : p.Cleavage)
    {a b : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b)
    (x : Fiber p (unop a.as)) :
    ((toPseudofunctor.uniqueEquivalence chi₁ chi₂).hom.naturality f).hom.toNatTrans.app x =
      (Reindex.uniqueIsoApp chi₁ chi₂ f.as.unop x).hom := sorry

/-- Objectwise, inverse naturality of the forward transformation is the inverse canonical
reindexing comparison. -/
@[simp]
theorem toPseudofunctor.uniqueEquivalence.forward.naturality.inv.app
    (chi₁ chi₂ : p.Cleavage)
    {a b : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b)
    (x : Fiber p (unop a.as)) :
    ((toPseudofunctor.uniqueEquivalence chi₁ chi₂).hom.naturality f).inv.toNatTrans.app x =
      (Reindex.uniqueIsoApp chi₁ chi₂ f.as.unop x).inv := sorry

/-- Objectwise, naturality of the inverse transformation is the canonical reindexing
comparison in the reverse direction. -/
@[simp]
theorem toPseudofunctor.uniqueEquivalence.inverse.naturality.hom.app
    (chi₁ chi₂ : p.Cleavage)
    {a b : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b)
    (x : Fiber p (unop a.as)) :
    ((toPseudofunctor.uniqueEquivalence chi₁ chi₂).inv.naturality f).hom.toNatTrans.app x =
      (Reindex.uniqueIsoApp chi₂ chi₁ f.as.unop x).hom := sorry

/-- Objectwise, inverse naturality of the inverse transformation is the inverse canonical
reindexing comparison in the reverse direction. -/
@[simp]
theorem toPseudofunctor.uniqueEquivalence.inverse.naturality.inv.app
    (chi₁ chi₂ : p.Cleavage)
    {a b : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b)
    (x : Fiber p (unop a.as)) :
    ((toPseudofunctor.uniqueEquivalence chi₁ chi₂).inv.naturality f).inv.toNatTrans.app x =
      (Reindex.uniqueIsoApp chi₂ chi₁ f.as.unop x).inv := sorry

/-- The canonical pseudofunctor equivalence from a cleavage to itself is the identity
equivalence. -/
@[simp]
theorem toPseudofunctor.uniqueEquivalence.self
    (chi : p.Cleavage) :
    toPseudofunctor.uniqueEquivalence chi chi =
      Bicategory.Equivalence.id chi.toPseudofunctor := sorry

/-- Reversing the canonical pseudofunctor equivalence exchanges the two cleavages. -/
@[simp]
theorem toPseudofunctor.uniqueEquivalence.symm
    (chi₁ chi₂ : p.Cleavage) :
    (toPseudofunctor.uniqueEquivalence chi₁ chi₂).symm =
      toPseudofunctor.uniqueEquivalence chi₂ chi₁ := sorry

/-- Canonical change-of-cleavage pseudofunctor equivalences compose transitively. -/
@[simp]
theorem toPseudofunctor.uniqueEquivalence.trans
    (chi₁ chi₂ chi₃ : p.Cleavage) :
    (toPseudofunctor.uniqueEquivalence chi₁ chi₂).trans
        (toPseudofunctor.uniqueEquivalence chi₂ chi₃) =
      toPseudofunctor.uniqueEquivalence chi₁ chi₃ := sorry

end Functor.Cleavage

end CategoryTheory
