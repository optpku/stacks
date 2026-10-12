/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.End.Power
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections.Power
import Mathlib.Tactic.CrossRefAttribute

/-!
# Endomorphism-power towers after derived global sections

The endomorphism-power comparison is owned generically by
`CategoryTheory.End.Power`.  This leaf records the reusable ringed-space specialization obtained
by applying derived global sections and a fixed homology functor.  The shifted inverse is the
fine-grained public API; the `IsIso` theorem is its pro-object bridge.
-/

@[expose] public section

open CategoryTheory CategoryTheory.SequentialInverseSystem
open CategoryTheory.End.Power
open AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.GlobalSections.Power

variable {X : RingedSpace.{u}} {A : Type v} [CommRing A]

/- Example 20.39.3 (0H3E): after scalar restriction along `α : A →+* Γ(X, 𝒪_X)`,
the quotient and two-term endomorphism-power towers have a shifted inverse after applying
`RΓ(X, -)` and `H^p`. -/
@[stacks 0H3E "cohomology tower shift inverse from endomorphism powers"]
theorem existsShiftInverse
    (α : A →+* globalSectionsRing X) (f : A)
    (ℱ : RingedSpace.Modules X) (p : ℤ)
    (hstable : kernelStabilizes (globalSectionMul (α f) ℱ)) :
    ∃ c : ℕ,
      ∃ comparison :
        SequentialInverseSystem.shift
            ((cokernelSystem (globalSectionMul (α f) ℱ)) ⋙
              moduleDerivedCohomologyFunctor X p) c ⟶
          (twoTermSystem (globalSectionMul (α f) ℱ)) ⋙
            moduleDerivedCohomologyFunctor X p,
        Pro.SequentialHom.IsShiftInverse
          (Functor.whiskerRight
            (augmentationSystem (globalSectionMul (α f) ℱ))
            (moduleDerivedCohomologyFunctor X p)) c comparison := sorry

/- Example 20.39.3 (0H3E): the canonical cohomology-level augmentation is invertible as a
sequential pro-morphism. -/
@[stacks 0H3E "cohomology tower canonical pro-isomorphism"]
theorem augmentation_isIso
    (α : A →+* globalSectionsRing X) (f : A)
    (ℱ : RingedSpace.Modules X) (p : ℤ)
    (hstable : kernelStabilizes (globalSectionMul (α f) ℱ)) :
    IsIso (Pro.SequentialHom.ofNatTrans
      (Functor.whiskerRight
        (augmentationSystem (globalSectionMul (α f) ℱ))
        (moduleDerivedCohomologyFunctor X p))).toHom := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.GlobalSections.Power
