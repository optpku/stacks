/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Grp

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj

namespace CategoryTheory.GrpObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {H G : C} [GrpObj G] (j : H ⟶ G)

/-- Bundle a group-object structure on `H` as an object of `Grp C`. -/
def asGrp (grpObj : GrpObj H) : Grp C where
  X := H
  grp := grpObj

/-- A group-object structure on `H` for which `j : H ⟶ G` preserves the unit and
multiplication. -/
structure Restriction where
  /-- The induced group-object structure on `H`. -/
  grpObj : GrpObj H
  /-- The induced group-object morphism from `H` to `G` with underlying map `j`. -/
  hom : asGrp grpObj ⟶ Grp.mk G
  /-- The underlying map of `hom` is `j`. -/
  hom_hom : hom.hom.hom = j

/-- Package the source of a restriction as a bundled group object. -/
abbrev Restriction.toGrp (R : Restriction j) : Grp C :=
  asGrp R.grpObj

/-- Package the inclusion underlying a restriction as a morphism of group objects. -/
abbrev Restriction.toHom (R : Restriction j) : R.toGrp ⟶ Grp.mk G :=
  R.hom

/-- The underlying object of `Restriction.toGrp` is `H`. -/
theorem Restriction.toGrp_X (R : Restriction j) : R.toGrp.X = H := rfl

/-- The underlying map of `Restriction.toHom` is `j`. -/
@[simp]
theorem Restriction.toHom_hom (R : Restriction j) : R.toHom.hom.hom = j := R.hom_hom

/-- Concrete factorizations through `H` of the unit, multiplication, and inverse of `G`. -/
structure Factorization where
  /-- The lift to `H` of the unit of `G`. -/
  one : 𝟙_ C ⟶ H
  /-- The lift to `H` of the multiplication of `G` restricted to `H ⊗ H`. -/
  mul : H ⊗ H ⟶ H
  /-- The lift to `H` of the inverse of `G` restricted to `H`. -/
  inv : H ⟶ H
  /-- The lifted unit composes with `j` to the unit of `G`. -/
  one_hom : one ≫ j = η[G]
  /-- The lifted multiplication composes with `j` to the restricted multiplication of `G`. -/
  mul_hom : mul ≫ j = (j ⊗ₘ j) ≫ μ[G]
  /-- The lifted inverse composes with `j` to the restricted inverse of `G`. -/
  inv_hom : inv ≫ j = j ≫ ι[G]

/-- The three equations defining factorization through `H`. -/
theorem Factorization.spec (F : Factorization j) :
    F.one ≫ j = η[G] ∧
      F.mul ≫ j = (j ⊗ₘ j) ≫ μ[G] ∧ F.inv ≫ j = j ≫ ι[G] := by
  exact ⟨F.one_hom, F.mul_hom, F.inv_hom⟩

/-- The unit of a compatible restriction commutes with its inclusion. -/
theorem Restriction.one_hom (R : Restriction j) :
    R.grpObj.toMonObj.one ≫ j = η[G] := by
  cases R with
  | mk grpObj hom hom_hom =>
      cases hom_hom
      exact IsMonHom.one_hom (f := hom.hom.hom)

/-- The multiplication of a compatible restriction commutes with its inclusion. -/
theorem Restriction.mul_hom (R : Restriction j) :
    R.grpObj.toMonObj.mul ≫ j = (j ⊗ₘ j) ≫ μ[G] := by
  cases R with
  | mk grpObj hom hom_hom =>
      cases hom_hom
      exact IsMonHom.mul_hom (f := hom.hom.hom)

/-- The inverse operation of a compatible restriction commutes with its inclusion. -/
theorem Restriction.inv_hom (R : Restriction j) :
    R.grpObj.inv ≫ j = j ≫ ι[G] := by
  cases R with
  | mk grpObj hom hom_hom =>
      cases hom_hom
      exact CategoryTheory.GrpObj.inv_hom (f := hom.hom.hom)

/-- A compatible restriction yields the three factor maps. -/
def Restriction.toFactorization (R : Restriction j) : Factorization j where
  one := R.grpObj.toMonObj.one
  mul := R.grpObj.toMonObj.mul
  inv := R.grpObj.inv
  one_hom := R.one_hom
  mul_hom := R.mul_hom
  inv_hom := R.inv_hom

variable [Mono j]

/-- The lifted operations satisfy the left unit law because `j` is a monomorphism. -/
theorem Factorization.one_mul (F : Factorization j) :
    (F.one ▷ H) ≫ F.mul = (λ_ H).hom := by
  rw [← cancel_mono j]
  calc
    ((F.one ▷ H) ≫ F.mul) ≫ j
        = (F.one ▷ H) ≫ (j ⊗ₘ j) ≫ μ[G] := by
            rw [Category.assoc, F.mul_hom]
    _ = ((F.one ≫ j) ⊗ₘ j) ≫ μ[G] := by
          rw [whiskerRight_comp_tensorHom_assoc]
    _ = (η[G] ⊗ₘ j) ≫ μ[G] := by
          rw [F.one_hom]
    _ = (λ_ H).hom ≫ j := by
          simpa using MonObj.one_mul_hom (M := G) (f := j)

/-- The lifted operations satisfy the right unit law because `j` is a monomorphism. -/
theorem Factorization.mul_one (F : Factorization j) :
    (H ◁ F.one) ≫ F.mul = (ρ_ H).hom := by
  rw [← cancel_mono j]
  calc
    ((H ◁ F.one) ≫ F.mul) ≫ j
        = (H ◁ F.one) ≫ (j ⊗ₘ j) ≫ μ[G] := by
            rw [Category.assoc, F.mul_hom]
    _ = (j ⊗ₘ (F.one ≫ j)) ≫ μ[G] := by
          rw [whiskerLeft_comp_tensorHom_assoc]
    _ = (j ⊗ₘ η[G]) ≫ μ[G] := by
          rw [F.one_hom]
    _ = (ρ_ H).hom ≫ j := by
          simpa using MonObj.mul_one_hom (M := G) (f := j)

/-- The lifted multiplication is associative because `j` is a monomorphism. -/
theorem Factorization.mul_assoc (F : Factorization j) :
    (F.mul ▷ H) ≫ F.mul =
      (α_ H H H).hom ≫ (H ◁ F.mul) ≫ F.mul := by
  rw [← cancel_mono j]
  calc
    ((F.mul ▷ H) ≫ F.mul) ≫ j
        = (((j ⊗ₘ j) ≫ μ[G]) ⊗ₘ j) ≫ μ[G] := by
            rw [Category.assoc, F.mul_hom, whiskerRight_comp_tensorHom_assoc, F.mul_hom]
    _ = ((j ⊗ₘ j) ⊗ₘ j) ≫ (μ[G] ▷ G) ≫ μ[G] := by
          rw [tensorHom_comp_whiskerRight_assoc]
    _ = ((j ⊗ₘ j) ⊗ₘ j) ≫ (α_ G G G).hom ≫ (G ◁ μ[G]) ≫ μ[G] := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ ((j ⊗ₘ j) ⊗ₘ j) ≫ k) (MonObj.mul_assoc (X := G))
    _ = (α_ H H H).hom ≫ (j ⊗ₘ ((j ⊗ₘ j) ≫ μ[G])) ≫ μ[G] := by
          symm
          simpa [Category.assoc] using
            congrArg (fun k ↦ k ≫ μ[G])
              (Mathlib.Tactic.MonTauto.associator_hom_comp_tensorHom_tensorHom_comp
                (f := j) (g := j) (h := j) (gh := μ[G]))
    _ = (α_ H H H).hom ≫ (H ◁ F.mul) ≫ (j ⊗ₘ j) ≫ μ[G] := by
          calc
            (α_ H H H).hom ≫ (j ⊗ₘ ((j ⊗ₘ j) ≫ μ[G])) ≫ μ[G]
                = (α_ H H H).hom ≫ (j ⊗ₘ (F.mul ≫ j)) ≫ μ[G] := by
                    rw [← F.mul_hom]
            _ = (α_ H H H).hom ≫ (H ◁ F.mul) ≫ (j ⊗ₘ j) ≫ μ[G] := by
                  rw [← whiskerLeft_comp_tensorHom_assoc]
    _ = ((α_ H H H).hom ≫ (H ◁ F.mul) ≫ F.mul) ≫ j := by
          have hk :
              (α_ H H H).hom ≫ (H ◁ F.mul) ≫ ((j ⊗ₘ j) ≫ μ[G]) =
                (α_ H H H).hom ≫ (H ◁ F.mul) ≫ (F.mul ≫ j) := by
            exact congrArg (fun k ↦ (α_ H H H).hom ≫ (H ◁ F.mul) ≫ k) F.mul_hom.symm
          simpa [Category.assoc] using hk

/-- The lifted inverse satisfies the left inverse law because `j` is a monomorphism. -/
theorem Factorization.left_inv (F : Factorization j) :
    lift F.inv (𝟙 H) ≫ F.mul = toUnit H ≫ F.one := by
  rw [← cancel_mono j]
  calc
    (lift F.inv (𝟙 H) ≫ F.mul) ≫ j
        = lift F.inv (𝟙 H) ≫ (j ⊗ₘ j) ≫ μ[G] := by
            rw [Category.assoc, F.mul_hom]
    _ = lift (F.inv ≫ j) (𝟙 H ≫ j) ≫ μ[G] := by
          rw [lift_map_assoc]
    _ = lift (j ≫ ι[G]) j ≫ μ[G] := by
          rw [F.inv_hom, Category.id_comp]
    _ = toUnit H ≫ η[G] := by
          simpa using GrpObj.lift_comp_inv_left (f := j)
    _ = (toUnit H ≫ F.one) ≫ j := by
          rw [Category.assoc, F.one_hom]

/-- The lifted inverse satisfies the right inverse law because `j` is a monomorphism. -/
theorem Factorization.right_inv (F : Factorization j) :
    lift (𝟙 H) F.inv ≫ F.mul = toUnit H ≫ F.one := by
  rw [← cancel_mono j]
  calc
    (lift (𝟙 H) F.inv ≫ F.mul) ≫ j
        = lift (𝟙 H) F.inv ≫ (j ⊗ₘ j) ≫ μ[G] := by
            rw [Category.assoc, F.mul_hom]
    _ = lift (𝟙 H ≫ j) (F.inv ≫ j) ≫ μ[G] := by
          rw [lift_map_assoc]
    _ = lift j (j ≫ ι[G]) ≫ μ[G] := by
          rw [F.inv_hom, Category.id_comp]
    _ = toUnit H ≫ η[G] := by
          simpa using GrpObj.lift_comp_inv_right (f := j)
    _ = (toUnit H ≫ F.one) ≫ j := by
          rw [Category.assoc, F.one_hom]

/-- The explicit group-object structure induced by factor maps through a monomorphism. -/
@[implicit_reducible]
def Factorization.toGrpObj (F : Factorization j) : GrpObj H where
  one := F.one
  mul := F.mul
  inv := F.inv
  one_mul := F.one_mul
  mul_one := F.mul_one
  mul_assoc := F.mul_assoc
  left_inv := F.left_inv
  right_inv := F.right_inv

/-- The inclusion preserves the group-object unit and multiplication induced by factorization. -/
def Factorization.toHom (F : Factorization j) : asGrp F.toGrpObj ⟶ Grp.mk G :=
  Grp.homMk'' j F.one_hom F.mul_hom

/-- The underlying map of `Factorization.toHom` is `j`. -/
@[simp]
theorem Factorization.toHom_hom (F : Factorization j) : F.toHom.hom.hom = j := rfl

/-- Construct a compatible group-object restriction from explicit factor maps. -/
def Factorization.toRestriction (F : Factorization j) : Restriction j where
  grpObj := F.toGrpObj
  hom := F.toHom
  hom_hom := F.toHom_hom

/-- Converting factor maps to a restriction and back recovers the original factor maps. -/
theorem Factorization.toRestriction_toFactorization (F : Factorization j) :
    F.toRestriction.toFactorization = F := by
  cases F
  rfl

/-- Converting a restriction to factor maps and back recovers the original restriction. -/
theorem Restriction.toFactorization_toRestriction (R : Restriction j) :
    R.toFactorization.toRestriction = R := by
  cases R with
  | mk grpObj hom hom_hom =>
      let hj : Mono j := inferInstance
      cases hom_hom
      -- Local instance justification (defeq pin): retain monicity after rewriting the fixed map to the bundled underlying map.
      let _ : Mono hom.hom.hom := hj
      let R' : Restriction hom.hom.hom := ⟨grpObj, hom, rfl⟩
      have hgrp : R'.toFactorization.toRestriction.grpObj = grpObj := by
        apply GrpObj.ext
        apply MonObj.ext
        rfl
      dsimp [R'] at hgrp
      cases hgrp
      have hhom : R'.toFactorization.toRestriction.hom = hom := by
        apply Grp.hom_ext
        rfl
      dsimp [R'] at hhom
      cases hhom
      rfl

/-- For a monomorphism, factor maps are equivalent to a compatible group-object restriction. -/
def Factorization.equivRestriction : Factorization j ≃ Restriction j where
  toFun := Factorization.toRestriction j
  invFun := Restriction.toFactorization j
  left_inv := Factorization.toRestriction_toFactorization j
  right_inv := Restriction.toFactorization_toRestriction j

/-- The forward map of `Factorization.equivRestriction` constructs the induced restriction. -/
theorem Factorization.equivRestriction_apply (F : Factorization j) :
    equivRestriction j F = F.toRestriction := by
  rfl

/-- The inverse map of `Factorization.equivRestriction` extracts the three factor maps. -/
theorem Factorization.equivRestriction_symm_apply (R : Restriction j) :
    (equivRestriction j).symm R = R.toFactorization := by
  rfl

end CategoryTheory.GrpObj
