module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import stacks_project.Chap59.Definition_59_31_3_EtaleSupport

/-!
# Étale sections supported in a subset

The additive groups of small-étale abelian-sheaf sections on an object of
`X.Etale` whose étale section support lies in a given subset.
-/

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})

/-- The additive group of sections of an abelian sheaf `F` on an object `U` of
`X.Etale` whose étale section support is contained in `Z`. -/
def abelianSheafSectionsSupportedIn (U : X.Etale) (Z : Set U.left) :
    AddSubgroup (F.1.obj (op U)) where
  carrier := {σ | (abelianSheafSectionSupport F U σ : Set U.left) ⊆ Z}
  zero_mem' := sorry
  add_mem' := sorry
  neg_mem' := sorry

/-- Membership in supported étale sections is containment of étale section support. -/
theorem mem_abelianSheafSectionsSupportedIn_iff (U : X.Etale) (Z : Set U.left)
    (σ : F.1.obj (op U)) :
    σ ∈ abelianSheafSectionsSupportedIn F U Z ↔
      (abelianSheafSectionSupport F U σ : Set U.left) ⊆ Z :=
  sorry

/-- Restriction of supported étale sections along a morphism of `X.Etale`. -/
def restrictSupportedIn {U U' : X.Etale} (φ : U' ⟶ U) (Z : Set U.left) :
    abelianSheafSectionsSupportedIn F U Z →+
      abelianSheafSectionsSupportedIn F U' (φ.left ⁻¹' Z) where
  toFun σ := ⟨F.1.map φ.op σ.val, sorry⟩
  map_zero' := sorry
  map_add' := sorry

/-- Restriction of supported étale sections acts by the étale sheaf restriction map. -/
theorem restrictSupportedIn_apply {U U' : X.Etale} (φ : U' ⟶ U) (Z : Set U.left)
    (σ : abelianSheafSectionsSupportedIn F U Z) :
    (restrictSupportedIn F φ Z σ).val = F.1.map φ.op σ.val :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
