/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap42.Lemma_42_47_1_LocalizedClass
public import stacks_project.Chap42.Lemma_42_47_8_Additivity
public import stacks_project.Chap42.Lemma_42_47_8_Cutoff
public import stacks_project.Chap42.Lemma_42_47_11_IntersectionProduct
public import stacks_project.Chap42.Lemma_42_47_11_Pullback
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

/-- Lemma 42.47.8 (1): on a set-theoretic closed cover, mixed cutoff Chern series of
perfect complexes with defined Chern classes and intersection rank bounds strictly less
than `p` and `q` are ambient-multiplicative for biproducts in degrees strictly less
than `p + q`. -/
@[stacks 0FAL]
theorem cutoffChernClass_biprod_lt
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
      ((RingedSpace.modulePullbackDerived
        (pullback.snd i₁ i₂ ≫ i₂).toShHom).obj E) 0 p)
    (rankF : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      ((RingedSpace.modulePullbackDerived
        (pullback.snd i₁ i₂ ≫ i₂).toShHom).obj F) 0 q)
    (classes : ChernClass.Theory δ X.hom) (n : ℕ) (hn : n < p + q) :
    totalClass δ X.hom classes (E ⊞ F)
        (perfectE.biprod perfectF) (definedE.biprod definedF) n =
      mul δ X.hom
        (totalClass δ X.hom classes E perfectE definedE)
        (totalClass δ X.hom classes F perfectF definedF) n := sorry

/-- Lemma 42.47.8 (2): on a set-theoretic closed cover, mixed cutoff Chern series of
perfect complexes with defined Chern classes and intersection rank bounds strictly less
than `p` and `q` are multiplicative for biproducts as a mixed Cauchy product in
degrees at least `p + q`. -/
@[stacks 0FAL]
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
      ((RingedSpace.modulePullbackDerived
        (pullback.snd i₁ i₂ ≫ i₂).toShHom).obj E) 0 p)
    (rankF : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      ((RingedSpace.modulePullbackDerived
        (pullback.snd i₁ i₂ ≫ i₂).toShHom).obj F) 0 q)
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
        (localizedBiprod k))
    (n : ℕ) (hn : p + q ≤ n) :
    localizedBiprod n =
      mixedMul δ (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) p q n hn
        (fun i ↦ cutoffChernClass δ
          (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) p i
          (totalClass δ X.hom classes E perfectE definedE i) (localizedE i))
        (fun j ↦ cutoffChernClass δ
          (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) q j
          (totalClass δ X.hom classes F perfectF definedF j) (localizedF j)) :=
  sorry

end AlgebraicGeometry.LocalizedChern
