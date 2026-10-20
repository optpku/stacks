/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.K0.Support.ChernCharacter
public import stacks_project.Chap42.Definition_42_50_3_RationalBivariant

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry.BivariantClass.Nonnegative

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.K0WithSupport

variable {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
variable {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
variable (i : Z ⟶ X.left) [IsClosedImmersion i]

/-- The additive localized Chern character in the inferred integral-first rationalization. -/
def chernCharacter
    (hqc : ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (classes : ChernClass.Theory δ X.hom) :
    K0WithSupport X.left (Set.range i.base) →+
      RationalCompletion δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) :=
  let f := (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)
  let degreeGroup := fun p : ℕ ↦
    @TensorProduct.addCommGroup ℤ inferInstance (BivariantClass δ f (p : ℤ)) ℚ
      (BivariantClass.pointwiseAddCommGroup δ f (p : ℤ)) inferInstance
      (@AddCommGroup.toIntModule _ (BivariantClass.pointwiseAddCommGroup δ f (p : ℤ))) inferInstance
  let completionGroup := @Pi.addCommGroup ℕ (fun p ↦ Rational.Degree δ f p) degreeGroup
  let e := @AddEquiv.piCongrRight ℕ (fun p ↦ Rational.Degree δ f p)
    (fun p ↦ RationalDegree δ f p) (fun p ↦ (degreeGroup p).toAdd)
    (fun _ ↦ inferInstance) fun p ↦ (canonicalDegreeEquiv δ f p).symm.toAddEquiv
  @AddMonoidHom.comp _ _ _ inferInstance completionGroup.toAddZero inferInstance
    (@AddEquiv.toAddMonoidHom _ _ completionGroup.toAddZeroClass inferInstance e)
    (chernCharacterWithTheory δ i hqc classes)

/-- Coefficientwise rationalization identifies the inferred character with the character
in the explicit pointwise rationalization. -/
theorem chernCharacter_toCanonical
    (hqc : ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (classes : ChernClass.Theory δ X.hom)
    (a : K0WithSupport X.left (Set.range i.base)) :
    (fun p ↦ canonicalDegreeEquiv δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) p
      (chernCharacter δ i hqc classes a p)) =
        chernCharacterWithTheory δ i hqc classes a := by
  funext p
  exact (canonicalDegreeEquiv δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) p).apply_symm_apply _

end AlgebraicGeometry.Scheme.K0WithSupport

/- The inferred rationalization retains the supported-perfect character's original type. -/
#check
  (AlgebraicGeometry.Scheme.K0WithSupport.chernCharacter :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ]
      {X : Over S} [AlgebraicGeometry.LocallyOfFiniteType X.hom]
      {Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X.left)
      [AlgebraicGeometry.IsClosedImmersion i],
      (∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left)) →
      AlgebraicGeometry.ChernClass.Theory δ X.hom →
        AlgebraicGeometry.Scheme.K0WithSupport X.left (Set.range i.base) →+
          AlgebraicGeometry.BivariantClass.Nonnegative.RationalCompletion δ
            (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X))
