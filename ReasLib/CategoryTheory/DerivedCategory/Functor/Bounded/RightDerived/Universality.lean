module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Canonical
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.DeltaFunctor
public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor.Effaceable
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Universality of Bounded-Below Right Derived Delta Functors

The two theorems here are the acyclicity-based universal properties of the
cohomological delta functor supplied by the sibling `DeltaFunctor` leaf.
They are separated from the concrete comparison and connecting-morphism data
so users who only need a degreewise functor do not import the universality
layer.
-/

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open scoped CategoryTheory

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive] [hF : PreservesFiniteLimits F]
  [hQ : (𝟭 𝒜).toBoundedBelowDerived.IsLocalization
    (HomotopyCategory.Plus.quasiIso 𝒜)]
  (RF : DerivedCategory.Plus 𝒜 ⥤ DerivedCategory.Plus ℬ)
  (α : F.toBoundedBelowDerived ⟶ DerivedCategory.Plus.Qh ⋙ RF)
  [hRF : RF.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso 𝒜)]
  [RF.CommShift ℤ] [RF.IsTriangulated]

include hF hQ α hRF

/-- Stacks 05TE: if every object embeds into an object computing the
bounded-below right derived functor of a left exact additive functor, then
the resulting bounded-below cohomological delta functor is universal. -/
@[stacks 05TE]
theorem Functor.RightDerived.Universal.ofAcyclic
    (hacyclic : ∀ X : 𝒜, ∃ (Y : 𝒜) (i : X ⟶ Y), Mono i ∧
      RightAcyclic.Bounded F Y) :
    CohomologicalDeltaFunctor.IsUniversal (Functor.RightDerived.cohomological RF) := sorry

/-- A mono-embedding class of bounded right-acyclic objects supplies the
universality hypothesis without exposing chosen embeddings downstream. -/
@[stacks 05TE "universality from enough bounded right-acyclic objects"]
theorem Functor.RightDerived.Universal.ofHasMonoEmbedding
    [ObjectProperty.HasMonoEmbedding (Functor.RightAcyclic.Bounded F)] :
    CohomologicalDeltaFunctor.IsUniversal
      (Functor.RightDerived.cohomological RF) := sorry

end

section Canonical

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive] [hF : PreservesFiniteLimits F]
  [hQ : (𝟭 𝒜).toBoundedBelowDerived.IsLocalization
    (HomotopyCategory.Plus.quasiIso 𝒜)]
  [hAcyclic : ObjectProperty.HasMonoEmbedding (Functor.RightAcyclic.Bounded F)]

include hF hQ hAcyclic

/-- The cohomological delta functor of the canonical bounded-below right
derived model is universal when bounded right-acyclic objects provide mono
embeddings. -/
@[stacks 05TE "universality of the canonical bounded-below right-derived delta functor"]
theorem Functor.RightDerived.Bounded.cohomological_isUniversal :
    CohomologicalDeltaFunctor.IsUniversal
      (Functor.RightDerived.cohomological
        (Functor.RightDerived.Bounded.functor F)) := sorry

/-- Universality of the canonical bounded-below right-derived delta functor
is available to typeclass search. -/
@[stacks 05TE "canonical bounded-below right-derived universality instance"]
instance Functor.RightDerived.Bounded.cohomological.isUniversal :
    CohomologicalDeltaFunctor.IsUniversal
      (Functor.RightDerived.cohomological
        (Functor.RightDerived.Bounded.functor F)) := sorry

end Canonical

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive] [hF : PreservesFiniteLimits F]
  [hInjective : HasInjectiveResolutions 𝒜]
  [hRU : (Functor.Homotopy.toDerived F).HasRightDerivedFunctor
    (HomotopyCategory.quasiIso 𝒜 (up ℤ))]
  [hQ : (𝟭 𝒜).toBoundedBelowDerived.IsLocalization
    (HomotopyCategory.Plus.quasiIso 𝒜)]
  (RF : DerivedCategory.Plus 𝒜 ⥤ DerivedCategory.Plus ℬ)
  (α : F.toBoundedBelowDerived ⟶ DerivedCategory.Plus.Qh ⋙ RF)
  [hRF : RF.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso 𝒜)]
  [RF.CommShift ℤ] [RF.IsTriangulated]

include hF hInjective hRU hQ α hRF

/-- If the bounded-below right derived family agrees degreewise with the
unbounded right derived family and every object embeds into an unbounded
right-acyclic object, the bounded-below cohomological delta functor is
universal. -/
@[stacks 05TE]
theorem Functor.RightDerived.Universal.ofComparison
    (hcompare : ∀ n : ℕ, IsIsomorphic (Functor.RightDerived.degree RF n) (F.rightDerived n))
    (hacyclic : ∀ X : 𝒜, ∃ (Y : 𝒜) (i : X ⟶ Y), Mono i ∧ RightAcyclic F Y) :
    CohomologicalDeltaFunctor.IsUniversal (Functor.RightDerived.cohomological RF) := sorry

end

end CategoryTheory
