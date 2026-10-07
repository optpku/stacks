module

public import ReasLib.Algebra.Homology.DerivedCategory.RelativeTensor
import StacksCheckRecall

/-!
# Definition 64.12.1

Finite Tor-dimension for objects of `DerivedCategory (ModuleCat R)` over a possibly
noncommutative ring.
-/

@[expose] public section

open CategoryTheory

universe u

/- Definition 64.12.1 (1): `K : DerivedCategory (ModuleCat R)` has finite Tor-dimension when
some `a, b : ℤ` make `HasTorAmplitudeIn K a b`. -/
@[stacks 03TN]
#check (CategoryTheory.DerivedCategory.RelativeTensor.HasFiniteTorDimension :
  ∀ {R : Type u} [Ring R], DerivedCategory (ModuleCat.{u} R) → Prop)

/- Definition 64.12.1 (2): finite Tor-dimension is the existence of a Tor-amplitude interval. -/
@[stacks 03TN] #check (CategoryTheory.DerivedCategory.RelativeTensor.hasFiniteTorDimension_iff :
  ∀ {R : Type u} [Ring R] (K : DerivedCategory (ModuleCat.{u} R)),
    CategoryTheory.DerivedCategory.RelativeTensor.HasFiniteTorDimension K ↔
      ∃ a b : ℤ, CategoryTheory.DerivedCategory.RelativeTensor.HasTorAmplitudeIn K a b)

/- Definition 64.12.1 (3): `HasTorAmplitudeIn K a b` means that for every right module `N` and
every `i ∉ Set.Icc a b`, the homology of `derivedTensorRight N K` vanishes. -/
@[stacks 03TN] #check (CategoryTheory.DerivedCategory.RelativeTensor.hasTorAmplitudeIn_iff_homology :
  ∀ {R : Type u} [Ring R] (K : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ),
    CategoryTheory.DerivedCategory.RelativeTensor.HasTorAmplitudeIn K a b ↔
      ∀ (N : ModuleCat.{u} Rᵐᵒᵖ) (i : ℤ), i ∉ Set.Icc a b →
        CategoryTheory.Limits.IsZero
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} ℤ) i).obj
            (CategoryTheory.DerivedCategory.RelativeTensor.derivedTensorRight N K)))
