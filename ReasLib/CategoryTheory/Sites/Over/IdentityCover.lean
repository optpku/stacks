module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Covers of the identity object in a slice site

This module gives the canonical correspondence between covers of `U` and covers of the identity
object `Over.mk (𝟙 U)` in the induced slice site `J.over U`.  It is useful whenever a construction
is naturally formulated over the slice site but its local data are indexed by base-site covers.
-/

@[expose] public section

universe u v

namespace CategoryTheory

namespace GrothendieckTopology.Cover

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

/-- The arrows of a base cover form a covering family at the identity object of the induced slice
site. This is the family-level form of `Cover.overIdentity`, used in sheaf extensionality. -/
theorem overIdentity_ofArrows_mem {U : C} (S : J.Cover U) :
    Sieve.ofArrows
      (fun I : S.Arrow => Over.mk I.f)
      (fun I => (Over.homMk I.f (Category.comp_id I.f) :
        Over.mk I.f ⟶ Over.mk (𝟙 U))) ∈
      (J.over U) (Over.mk (𝟙 U)) := sorry

/-- Regard a cover of `U` as a cover of the identity object in the slice site over `U`. -/
noncomputable def overIdentity {U : C} (S : J.Cover U) :
    (J.over U).Cover (Over.mk (𝟙 U)) :=
  ⟨(Sieve.overEquiv (Over.mk (𝟙 U))).symm S.1,
    GrothendieckTopology.overEquiv_symm_mem_over J (Over.mk (𝟙 U)) S.1 S.condition⟩

/-- Push a cover of the identity object in the slice site over `U` down to a cover of `U`. -/
noncomputable def baseOfOverIdentity {U : C}
    (S : (J.over U).Cover (Over.mk (𝟙 U))) : J.Cover U :=
  ⟨Sieve.overEquiv (Over.mk (𝟙 U)) S.1, (J.mem_over_iff S.1).1 S.condition⟩

/-- A refinement of covers at the identity object of a slice site induces the corresponding
refinement of the base covers. -/
theorem baseOfOverIdentity_le_of_hom {U : C}
    {S T : (J.over U).Cover (Over.mk (𝟙 U))} (h : S ⟶ T) :
    (baseOfOverIdentity S : Sieve U) ≤ baseOfOverIdentity T := sorry

/-- Transport a refinement of identity-slice covers to a refinement of base covers. -/
noncomputable def baseOfOverIdentityHom {U : C}
    {S T : (J.over U).Cover (Over.mk (𝟙 U))} (h : S ⟶ T) :
    baseOfOverIdentity S ⟶ baseOfOverIdentity T :=
  homOfLE (baseOfOverIdentity_le_of_hom h)

/-- A refinement of base covers induces the corresponding refinement of their covers at the
identity object of the slice site. -/
theorem overIdentity_le_of_hom {U : C} {S T : J.Cover U} (h : S ⟶ T) :
    (overIdentity S : Sieve (Over.mk (𝟙 U))) ≤ overIdentity T := sorry

/-- Transport a refinement of base covers to a refinement of identity-slice covers. -/
noncomputable def overIdentityHom {U : C} {S T : J.Cover U} (h : S ⟶ T) :
    overIdentity S ⟶ overIdentity T :=
  homOfLE (overIdentity_le_of_hom h)

/-- Pushing a base cover to the identity slice object and back is the identity. -/
@[simp]
theorem baseOfOverIdentity_overIdentity {U : C} (S : J.Cover U) :
    baseOfOverIdentity (overIdentity S) = S := sorry

/-- Pushing an identity-slice cover down to the base and back is the identity. -/
@[simp]
theorem overIdentity_baseOfOverIdentity {U : C}
    (S : (J.over U).Cover (Over.mk (𝟙 U))) :
    overIdentity (baseOfOverIdentity S) = S := sorry

/-- Covers of `U` are canonically equivalent to covers of the identity object in the slice site
over `U`. Refinements are transported by `overIdentityHom` and `baseOfOverIdentityHom`. -/
noncomputable def overIdentityEquiv {U : C} :
    J.Cover U ≃ (J.over U).Cover (Over.mk (𝟙 U)) where
  toFun := overIdentity
  invFun := baseOfOverIdentity
  left_inv := baseOfOverIdentity_overIdentity
  right_inv := overIdentity_baseOfOverIdentity

/-- The top identity-slice cover pushes down to the top base cover. -/
@[simp]
theorem baseOfOverIdentity_top {U : C} :
    baseOfOverIdentity (J := J) (⊤ : (J.over U).Cover (Over.mk (𝟙 U))) = ⊤ := sorry

/-- Pushing down an intersection with an identity-slice cover preserves the corresponding
intersection with the base cover. -/
theorem baseOfOverIdentity_inf_overIdentity {U : C}
    (S : (J.over U).Cover (Over.mk (𝟙 U))) (R : J.Cover U) :
    baseOfOverIdentity (S ⊓ overIdentity R) = baseOfOverIdentity S ⊓ R := sorry

/-- An arrow in the base cover pushed down from an identity-slice cover determines the
corresponding arrow in that slice cover. -/
theorem baseOfOverIdentity_arrow_mem {U : C}
    (S : (J.over U).Cover (Over.mk (𝟙 U)))
    (I : (baseOfOverIdentity S).Arrow) :
    S.1 (Over.homMk I.f : Over.mk (I.f ≫ 𝟙 U) ⟶ Over.mk (𝟙 U)) := sorry

end GrothendieckTopology.Cover

end CategoryTheory
