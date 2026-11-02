/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Category.TopCommRingCat
public import Mathlib.Topology.Category.TopCat.Limits.Basic

/-!
# Limits of topological commutative rings
-/

@[expose] public section

universe v u w

open CategoryTheory CategoryTheory.Limits

namespace TopCommRingCat

section LimitCone

variable {J : Type v} [Category.{w} J] (F : J ⥤ TopCommRingCat.{max v u})

/-- The compatible families form a subring of the product of the underlying rings. -/
def sectionsSubring : Subring (∀ j, F.obj j) :=
  RingCat.sectionsSubring
    (F ⋙ forget₂ TopCommRingCat CommRingCat ⋙ forget₂ CommRingCat RingCat)

/-- The limit cone consists of compatible families with the subspace topology of the product. -/
def limitCone : Cone F where
  pt := TopCommRingCat.of (sectionsSubring F)
  π :=
    { app := fun j =>
        ⟨(Pi.evalRingHom (fun j => F.obj j) j).comp (sectionsSubring F).subtype,
          (continuous_apply j).comp continuous_subtype_val⟩
      naturality i j f := by
        apply Subtype.ext
        apply RingHom.ext
        intro x
        exact (x.2 f).symm }

/-- A cone induces the continuous ring homomorphism sending a point to its components. -/
def limitConeIsLimit : IsLimit (limitCone F) where
  lift s :=
    ⟨(RingHom.pi (fun j : J => (s.π.app j).1) : s.pt →+* ∀ j, F.obj j).codRestrict
        (sectionsSubring F) (by
          intro x i j f
          change (F.map f).1 ((s.π.app i).1 x) = (s.π.app j).1 x
          exact ConcreteCategory.congr_hom (s.w f) x),
      Continuous.subtype_mk (continuous_pi (fun j => (s.π.app j).2)) _⟩
  fac s j := by
    apply Subtype.ext
    apply RingHom.ext
    intro x
    rfl
  uniq s m h := by
    apply Subtype.ext
    apply RingHom.ext
    intro x
    apply Subtype.ext
    funext j
    exact ConcreteCategory.congr_hom (h j) x

/-- Forgetting the explicit limit cone gives the usual limit cone of topological spaces. -/
def forgetToTopCatLimitConeIsLimit :
    IsLimit ((forget₂ TopCommRingCat TopCat).mapCone (limitCone F)) :=
  TopCat.limitConeIsLimit (F ⋙ forget₂ TopCommRingCat TopCat)

/-- The same compatible families, with their coordinatewise ring operations, are a ring limit. -/
noncomputable def forgetToCommRingCatLimitConeIsLimit :
    IsLimit ((forget₂ TopCommRingCat CommRingCat).mapCone (limitCone F)) := by
  refine IsLimit.ofFaithful (forget CommRingCat)
    (Types.limitConeIsLimit (F ⋙ forget TopCommRingCat))
    (fun s => CommRingCat.ofHom
      ((RingHom.pi (fun j : J => (s.π.app j).hom) : s.pt →+* ∀ j, F.obj j).codRestrict
        (sectionsSubring F) (by
          intro x i j f
          change (F.map f).1 ((s.π.app i).hom x) = (s.π.app j).hom x
          exact ConcreteCategory.congr_hom (s.w f) x))) (fun s => rfl)

end LimitCone

/-- The category of topological commutative rings has all small limits. -/
@[stacks 0B23 "existence of limits in topological commutative rings"]
instance hasLimits : HasLimits TopCommRingCat.{u} where
  has_limits_of_shape _ _ :=
    { has_limit := fun F => ⟨⟨limitCone F, limitConeIsLimit F⟩⟩ }

/-- Forgetting a topological commutative ring to its topological space preserves all small limits. -/
@[stacks 0B23 "limits are preserved by the forgetful functor to topological spaces"]
instance forgetToTopCat_preservesLimits :
    PreservesLimits (forget₂ TopCommRingCat.{u} TopCat.{u}) where
  preservesLimitsOfShape :=
    { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit F)
          (forgetToTopCatLimitConeIsLimit F) }

/-- Forgetting a topological commutative ring to its commutative ring preserves all small limits. -/
@[stacks 0B23 "limits are preserved by the forgetful functor to commutative rings"]
instance forgetToCommRingCat_preservesLimits :
    PreservesLimits (forget₂ TopCommRingCat.{u} CommRingCat.{u}) where
  preservesLimitsOfShape :=
    { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit F)
          (forgetToCommRingCatLimitConeIsLimit F) }

end TopCommRingCat
