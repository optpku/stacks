/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.LocalizedExtension
public import ReasLib.AlgebraicGeometry.BivariantClass.Intersection
public import ReasLib.AlgebraicGeometry.BivariantClass.Cutoff.MixedProduct
public import ReasLib.AlgebraicGeometry.LocalizedChern.Cutoff
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Derived.Biproduct
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.VectorBundle.Biproduct
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Pullback

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

open ChernClass.Derived
open RingedSpace.ModuleDerived
open BivariantClass.Cutoff
open ChowCohomology.Nonnegative.Completion

/-- For a scheme covered by two closed subschemes, the complete cutoff total
Chern families of two perfect derived modules satisfy the Whitney product formula
when their restrictions to the first component are degree-zero vector bundles
with the specified strict rank bounds. The coefficients at and above each cutoff
are localized extensions of the Chern classes on the second component. -/
theorem cutoffChernClass_biprod
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ}
    [IsDimensionFunction δ] {X : Over S} [LocallyOfFiniteType X.hom]
    {X₁ X₂ : Scheme.{u}} (i₁ : X₁ ⟶ X.left) (i₂ : X₂ ⟶ X.left)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (cover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (E F : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfectE : RingedSpace.ModuleDerived.IsPerfect E)
    (perfectF : RingedSpace.ModuleDerived.IsPerfect F)
    (definedE : ChernClass.Derived.IsDefined E)
    (definedF : ChernClass.Derived.IsDefined F) (p q : ℕ)
    (rankE : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      ((RingedSpace.modulePullbackDerived i₁.toShHom).obj E) 0 p)
    (rankF : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      ((RingedSpace.modulePullbackDerived i₁.toShHom).obj F) 0 q)
    (classes : ChernClass.Theory δ X.hom)
    (localizedE localizedF localizedBiprod :
      (k : ℕ) → BivariantClass δ
        (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) (k : ℤ))
    (hlocalizedE : ∀ k : ℕ, p ≤ k →
      BivariantClass.IsLocalizedExtension δ X i₁ i₂ (k : ℤ)
        (totalClass δ (i₂ ≫ X.hom) (classes.reanchor (Over.mk (i₂ ≫ X.hom)))
          ((RingedSpace.modulePullbackDerived i₂.toShHom).obj E)
          (RingedSpace.modulePullbackDerived_isPerfect i₂.toShHom E perfectE)
          (IsDefined.pullback i₂ definedE) k)
        (localizedE k))
    (hlocalizedF : ∀ k : ℕ, q ≤ k →
      BivariantClass.IsLocalizedExtension δ X i₁ i₂ (k : ℤ)
        (totalClass δ (i₂ ≫ X.hom) (classes.reanchor (Over.mk (i₂ ≫ X.hom)))
          ((RingedSpace.modulePullbackDerived i₂.toShHom).obj F)
          (RingedSpace.modulePullbackDerived_isPerfect i₂.toShHom F perfectF)
          (IsDefined.pullback i₂ definedF) k)
        (localizedF k))
    (hlocalizedBiprod : ∀ k : ℕ, p + q ≤ k →
      BivariantClass.IsLocalizedExtension δ X i₁ i₂ (k : ℤ)
        (totalClass δ (i₂ ≫ X.hom) (classes.reanchor (Over.mk (i₂ ≫ X.hom)))
          ((RingedSpace.modulePullbackDerived i₂.toShHom).obj (E ⊞ F))
          (RingedSpace.modulePullbackDerived_isPerfect i₂.toShHom (E ⊞ F)
            (perfectE.biprod perfectF))
          (IsDefined.pullback i₂ (definedE.biprod definedF)) k)
        (localizedBiprod k)) :
    (fun n ↦ cutoffChernClass δ
      (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) (p + q) n
      (totalClass δ X.hom classes (E ⊞ F)
        (perfectE.biprod perfectF) (definedE.biprod definedF) n)
      (localizedBiprod n)) =
      familyMul δ (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) p q
        (fun i ↦ cutoffChernClass δ
          (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) p i
          (totalClass δ X.hom classes E perfectE definedE i) (localizedE i))
        (fun j ↦ cutoffChernClass δ
          (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) q j
          (totalClass δ X.hom classes F perfectF definedF j) (localizedF j)) := sorry

end AlgebraicGeometry.LocalizedChern
