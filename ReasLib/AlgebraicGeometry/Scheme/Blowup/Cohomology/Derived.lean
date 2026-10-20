/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.AffineDerived
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TensorProduct
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.TwistingSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor

/-!
# Derived cohomology of affine blowups

Above a cohomological cutoff for the blowup twists, twisted derived pullback followed by
derived global sections is computed by tensoring with the corresponding ideal power.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Scheme.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.IsBlowup

/-- For a Noetherian affine blowup, above a cutoff where the twists have no higher cohomology
and their global sections are ideal powers, derived global sections of the twisted derived
pullback of any module are isomorphic to its derived tensor product with that ideal power. -/
theorem derivedGlobalSectionsTwistedPullback
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)]
    (q₀ : ℕ)
    (hVanishing : ∀ {r i : ℕ}, q₀ ≤ r → 0 < i →
      IsZero (Scheme.Hom.cohomology p (twistingSheaf I p (r : ℤ)) i))
    (hSections : ∀ {r : ℕ}, q₀ ≤ r →
      IsIsomorphic (Scheme.Hom.cohomology p (twistingSheaf I p (r : ℤ)) 0)
        (ModuleCat.of A (I ^ r : Ideal A)))
    (q : ℕ) (hq : q₀ ≤ q) (M : ModuleCat A) :
    IsIsomorphic
      ((affineBaseModuleDerivedGlobalSectionsFunctor A p).obj
        (DerivedCategory.DerivedTensor.Right.obj (C := RingedSpace.Modules X.toRingedSpace)
          ((affineBaseModuleDerivedAssociatedFunctor A p).obj
            ((DerivedCategory.singleFunctor (ModuleCat A) 0).obj M))
          ((DerivedCategory.singleFunctor X.Modules 0).obj (twistingSheaf I p (q : ℤ)))))
      (DerivedCategory.DerivedTensor.Right.obj
        ((DerivedCategory.singleFunctor (ModuleCat A) 0).obj M)
        ((DerivedCategory.singleFunctor (ModuleCat A) 0).obj
          (ModuleCat.of A (I ^ q : Ideal A)))) := sorry

end AlgebraicGeometry.IsBlowup
