/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.Semilinear.RestrictScalars
public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.RestrictScalars

/-!
# Restricting the base of semilinear divided-power chain-DGA morphisms

The common-base restriction of a semilinear chain-DGA morphism preserves its divided-power
compatibility.  This gives a direct map between the two scalar restrictions, avoiding an
iterated restricted target and a later comparison isomorphism.
-/

@[expose] public section

noncomputable section

universe uQ uR uS uA

namespace DividedPowerChainAlgebra.SemilinearHom

variable {Q : Type uQ} {R : Type uR} {S : Type uS}
variable [CommRing Q] [CommRing R] [CommRing S]
variable {rho : Q →+* R} {tau : Q →+* S} {sigma : R →+* S}
-- The semilinear owner remains cross-universe.  This bundled-Hom bridge has one carrier
-- universe, inherited from the corresponding generic `ChainDGAlgebra` bridge.
variable {A : DividedPowerChainAlgebra.{uR, uA} R}
variable {B : DividedPowerChainAlgebra.{uS, uA} S}

/-- The common-base restriction of a semilinear divided-power morphism still commutes with the
total divided-power operations. -/
theorem restrictScalars_map_gamma (f : SemilinearHom sigma A B)
    (h : sigma.comp rho = tau) (n : ℕ)
    (x : (DividedPowerChainAlgebra.restrictScalars rho A).toChainDGAlgebra.nonnegativePart.evenPositivePart) :
    (f.toChainHom.restrictScalars h).nonnegativePart.evenMap
        ((DividedPowerChainAlgebra.restrictScalars rho A).gamma n x) =
      (DividedPowerChainAlgebra.restrictScalars tau B).gamma n
        ((f.toChainHom.restrictScalars h).nonnegativePart.evenPositiveMap x) := sorry

/-- Tag 09PQ: restrict a semilinear divided-power chain-DGA morphism on both sides to a common
base ring through a commutative scalar triangle. -/
@[stacks 09PQ "restriction of a semilinear divided-power morphism to a common base"]
def restrictScalars (f : SemilinearHom sigma A B)
    (h : sigma.comp rho = tau) :
    DividedPowerChainAlgebra.Hom
      (DividedPowerChainAlgebra.restrictScalars rho A)
      (DividedPowerChainAlgebra.restrictScalars tau B) where
  toChainHom := f.toChainHom.restrictScalars h
  map_gamma := restrictScalars_map_gamma f h

/-- The chain-DGA map underlying common-base restriction is the generic common-base restriction
of the semilinear chain-DGA map. -/
@[simp]
theorem restrictScalars_toChainHom (f : SemilinearHom sigma A B)
    (h : sigma.comp rho = tau) :
    (f.restrictScalars h).toChainHom = f.toChainHom.restrictScalars h := sorry

/-- Common-base restriction preserves the pointwise action of a semilinear divided-power
morphism. -/
@[simp]
theorem restrictScalars_apply (f : SemilinearHom sigma A B)
    (h : sigma.comp rho = tau) (n : ℤ)
    (x : (DividedPowerChainAlgebra.restrictScalars rho A).toChainDGAlgebra.X n) :
    f.restrictScalars h n x = f n x := sorry

/-- Common-base restriction preserves degreewise surjectivity. -/
theorem restrictScalars_surjective (f : SemilinearHom sigma A B)
    (h : sigma.comp rho = tau) (hf : f.Surjective) :
    (f.restrictScalars h).Surjective := sorry

/-- Common-base restriction preserves degreewise injectivity. -/
theorem restrictScalars_injective (f : SemilinearHom sigma A B)
    (h : sigma.comp rho = tau) (hf : f.Injective) :
    (f.restrictScalars h).Injective := sorry

/-- Common-base restriction preserves degreewise bijectivity. -/
theorem restrictScalars_bijective (f : SemilinearHom sigma A B)
    (h : sigma.comp rho = tau) (hf : f.Bijective) :
    (f.restrictScalars h).Bijective := sorry

end DividedPowerChainAlgebra.SemilinearHom
