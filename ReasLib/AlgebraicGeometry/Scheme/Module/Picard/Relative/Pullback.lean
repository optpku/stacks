/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Subfunctor.Image
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.Group
public import ReasLib.CategoryTheory.RepresentablePresheaf

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry MonoidalCategory CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.RelativePicard

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (X : SchemeOverField k) [Curve X] [Smooth X.hom] [Projective X.hom]

/-- The degree-zero Picard component is a group object. -/
instance instComponentZeroGrpObj : GrpObj (component X 0) :=
  componentZeroGrpObj X

/-- The structure morphism of the degree-zero Picard component is geometrically integral. -/
instance instGeometricallyIntegral_componentZero :
    GeometricallyIntegral (component X 0).hom := sorry

/-- The degree-zero Picard component of a smooth projective curve is an abelian variety. -/
instance instAbelianVariety_componentZero : AbelianVariety (component X 0) :=
  inferInstance

/-- Pullback along a curve endomorphism on the Picard presheaf. -/
def pullbackPresheaf (φ : X ⟶ X) : presheaf X ⟶ presheaf X where
  app T := TypeCat.ofHom (Scheme.Hom.picardPullback ((T.unop ◁ φ).left))
  naturality := sorry

/-- Pullback of Picard classes is computed by `Scheme.Hom.picardPullback`. -/
theorem pullbackPresheaf_app (φ : X ⟶ X) (T : (Over (Spec (CommRingCat.of k)))ᵒᵖ)
    (x : (presheaf X).obj T) :
    (pullbackPresheaf X φ).app T x =
      Scheme.Hom.picardPullback ((T.unop ◁ φ).left) x := sorry

/-- Pullback along the identity is the identity of the Picard presheaf. -/
theorem pullbackPresheaf_id : pullbackPresheaf X (𝟙 X) = 𝟙 (presheaf X) := sorry

/-- Picard pullback is contravariant under composition of curve endomorphisms. -/
theorem pullbackPresheaf_comp (φ ψ : X ⟶ X) :
    pullbackPresheaf X (φ ≫ ψ) =
      pullbackPresheaf X ψ ≫ pullbackPresheaf X φ := sorry

/-- Sheafification of Picard pullback along a curve endomorphism. -/
def pullbackFunctor (φ : X ⟶ X) : functor X ⟶ functor X :=
  (presheafToSheaf
      (Scheme.fppfTopology.over (Spec (CommRingCat.of k))) (Type (u + 1))).map
    (pullbackPresheaf X φ)

/-- Picard pullback preserves the degree-zero subfunctor. -/
theorem pullbackFunctor_range_degreeZero (φ : X ⟶ X) :
    Subfunctor.range ((degreeSubfunctor X 0).ι ≫ (pullbackFunctor X φ).hom) ≤
      degreeSubfunctor X 0 := sorry

/-- The degree-zero subfunctor map induced by Picard pullback. -/
def pullbackDegreeZero (φ : X ⟶ X) :
    (degreeSubfunctor X 0).toFunctor ⟶ (degreeSubfunctor X 0).toFunctor :=
  Subfunctor.lift ((degreeSubfunctor X 0).ι ≫ (pullbackFunctor X φ).hom)
    (pullbackFunctor_range_degreeZero X φ)

/-- The Jacobian endomorphism induced by pullback along a curve endomorphism. -/
def pullbackComponentHom (φ : X ⟶ X) : component X 0 ⟶ component X 0 :=
  (componentRepresentation X 0).map (componentRepresentation X 0)
    (pullbackDegreeZero X φ)

/-- Identity endomorphisms induce the identity on the Jacobian. -/
theorem pullbackComponentHom_id :
    pullbackComponentHom X (𝟙 X) = 𝟙 (component X 0) := sorry

/-- Jacobian pullback is contravariant in the curve endomorphism. -/
theorem pullbackComponentHom_comp (φ ψ : X ⟶ X) :
    pullbackComponentHom X (φ ≫ ψ) =
      pullbackComponentHom X ψ ≫ pullbackComponentHom X φ := sorry

/-- Pullback along a curve endomorphism preserves degree-zero Picard classes. -/
theorem picardPullback_mem_degreeClasses_zero (φ : X ⟶ X)
    (x : degreeClasses X 0) :
    Scheme.Hom.picardPullback φ.left x.1 ∈ degreeClasses X 0 := sorry

/-- On rational points of `Pic^0`, Jacobian pullback agrees with Picard pullback. -/
theorem pullbackComponentHom_picardPullback (φ : X ⟶ X)
    (x : degreeClasses X 0) :
    degreeClassToComponentPoint X 0 x ≫ pullbackComponentHom X φ =
      degreeClassToComponentPoint X 0
        ⟨Scheme.Hom.picardPullback φ.left x.1,
          picardPullback_mem_degreeClasses_zero X φ x⟩ := sorry

/-- Jacobian pullback of a curve endomorphism is a group-scheme morphism. -/
instance instIsMonHom_pullbackComponentHom (φ : X ⟶ X) :
    IsMonHom (pullbackComponentHom X φ) := sorry

end AlgebraicGeometry.RelativePicard
