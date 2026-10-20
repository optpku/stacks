module

public import ReasLib.CategoryTheory.Sites.Ringed.Map
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic

/-!
# Equivalences of explicit ringed sites

An equivalence identifies the underlying categories, their covering topologies,
and their structure sheaves.
-/

@[expose] public section

universe uC vC uD vD w

namespace CategoryTheory.RingedSiteMap

variable {C : Type uC} [Category.{vC} C]
  {D : Type uD} [Category.{vD} D]
  {J : GrothendieckTopology C} {O : Sheaf J RingCat.{w}}
  {K : GrothendieckTopology D} {P : Sheaf K RingCat.{w}}

/-- A ringed-site map is an equivalence when its base is a categorical equivalence
identifying the covering topologies and its structure-sheaf map is invertible. -/
def IsEquivalence (f : RingedSiteMap J O K P) : Prop :=
  Functor.IsEquivalence f.base ∧ f.base.IsDenseSubsite K J ∧ IsIso f.structureSheafMap

/-- Equivalence of a ringed-site map means equivalence of its base category,
the dense-subsite condition, and invertibility of its structure-sheaf map. -/
theorem isEquivalence_iff (f : RingedSiteMap J O K P) :
    IsEquivalence f ↔
      Functor.IsEquivalence f.base ∧ f.base.IsDenseSubsite K J ∧
        IsIso f.structureSheafMap := Iff.rfl

end CategoryTheory.RingedSiteMap
