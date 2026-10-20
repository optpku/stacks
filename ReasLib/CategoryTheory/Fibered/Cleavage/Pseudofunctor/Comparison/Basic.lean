module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.PointwiseEquivalence.Equivalence
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.IndexedFunctor.Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Independence of the fiber pseudofunctor from a cleavage

Two cleavages of the same projection have the same fiber categories and canonically isomorphic
reindexing functors. This leaf converts the shared identity-base indexed comparison into a
strong transformation and a pseudofunctor equivalence. All nontrivial arrow data comes from
`Reindex.uniqueIso`.
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

/-- The canonical strong transformation between the fiber pseudofunctors associated to two
cleavages. It is the strong-transformation presentation of the shared identity-on-fibers
`Indexed.comparison`. -/
noncomputable def toPseudofunctor.uniqueStrongTrans
    (chi₁ chi₂ : p.Cleavage) :
    Pseudofunctor.StrongTrans chi₁.toPseudofunctor chi₂.toPseudofunctor :=
  (Indexed.comparison chi₁ chi₂).toStrongTrans

/-- Components of the canonical strong change-of-cleavage transformation are identity
functors. -/
@[simp]
theorem toPseudofunctor.uniqueStrongTrans.app
    (chi₁ chi₂ : p.Cleavage) (a : LocallyDiscrete Cᵒᵖ) :
    (toPseudofunctor.uniqueStrongTrans chi₁ chi₂).app a =
      𝟙 (chi₁.toPseudofunctor.obj a) := sorry

/-- The naturality isomorphism of the canonical strong change-of-cleavage transformation is the
strong-transformation form of indexed naturality. -/
@[simp]
theorem toPseudofunctor.uniqueStrongTrans.naturality
    (chi₁ chi₂ : p.Cleavage)
    {a b : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b) :
    (toPseudofunctor.uniqueStrongTrans chi₁ chi₂).naturality f =
      (Indexed.comparison chi₁ chi₂).toStrongTransNaturality f := sorry

/-- Returning the canonical strong change-of-cleavage transformation to the indexed
presentation recovers the shared indexed comparison. -/
@[simp]
theorem toPseudofunctor.uniqueStrongTrans.toIndexedFunctor
    (chi₁ chi₂ : p.Cleavage) :
    (toPseudofunctor.uniqueStrongTrans chi₁ chi₂).toIndexedFunctor =
      Indexed.comparison chi₁ chi₂ := sorry

/-- Objectwise, the forward strong-transformation constraint is the canonical forward
change-of-cleavage comparison. -/
@[simp]
theorem toPseudofunctor.uniqueStrongTrans.naturality.hom.app
    (chi₁ chi₂ : p.Cleavage)
    {a b : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b)
    (x : Fiber p (unop a.as)) :
    ((toPseudofunctor.uniqueStrongTrans chi₁ chi₂).naturality f).hom.toNatTrans.app x =
      (Reindex.uniqueIsoApp chi₁ chi₂ f.as.unop x).hom := sorry

/-- Objectwise, the inverse strong-transformation constraint is the canonical inverse
change-of-cleavage comparison. -/
@[simp]
theorem toPseudofunctor.uniqueStrongTrans.naturality.inv.app
    (chi₁ chi₂ : p.Cleavage)
    {a b : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b)
    (x : Fiber p (unop a.as)) :
    ((toPseudofunctor.uniqueStrongTrans chi₁ chi₂).naturality f).inv.toNatTrans.app x =
      (Reindex.uniqueIsoApp chi₁ chi₂ f.as.unop x).inv := sorry

/-- Pointwise identity equivalence data for the canonical strong change-of-cleavage
transformation. -/
noncomputable def toPseudofunctor.uniquePointwiseEquivalence
    (chi₁ chi₂ : p.Cleavage) :
    Pseudofunctor.StrongTrans.PointwiseEquivalence
      (toPseudofunctor.uniqueStrongTrans chi₁ chi₂) :=
  Pseudofunctor.StrongTrans.PointwiseEquivalence.ofComponents
    (fun _ ↦ Bicategory.Equivalence.id _)
    (fun _ ↦ Iso.refl _)

/-- Fiber pseudofunctors associated to any two cleavages are canonically equivalent. -/
@[stacks 02XO]
noncomputable def toPseudofunctor.uniqueEquivalence
    (chi₁ chi₂ : p.Cleavage) :
    chi₁.toPseudofunctor ≌ chi₂.toPseudofunctor :=
  (toPseudofunctor.uniquePointwiseEquivalence chi₁ chi₂).toEquivalence

/-- The forward strong transformation of the canonical pseudofunctor equivalence is the named
change-of-cleavage transformation. -/
@[simp]
theorem toPseudofunctor.uniqueEquivalence.hom
    (chi₁ chi₂ : p.Cleavage) :
    (toPseudofunctor.uniqueEquivalence chi₁ chi₂).hom =
      toPseudofunctor.uniqueStrongTrans chi₁ chi₂ := sorry

/-- The indexed presentation of the forward canonical pseudofunctor equivalence is the shared
change-of-cleavage comparison. -/
@[simp]
theorem toPseudofunctor.uniqueEquivalence.hom.toIndexedFunctor
    (chi₁ chi₂ : p.Cleavage) :
    (toPseudofunctor.uniqueEquivalence chi₁ chi₂).hom.toIndexedFunctor =
      Indexed.comparison chi₁ chi₂ := sorry

/- Data audit (mathlib 4.32): the component functors are literal identities and the
nontrivial naturality data is assembled from `Reindex.uniqueIso`, whose ambient arrow data is
clean up to `propext`, `Classical.choice`, and `Quot.sound`. Any `sorryAx` in the assembled
strong transformation or equivalence is confined to naturality, coherence, and inverse-law
proof fields. -/

end Functor.Cleavage

end CategoryTheory
