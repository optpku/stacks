/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.RestrictScalars

/-!
# Restricting the base of semilinear chain-DGA morphisms

A semilinear morphism along `sigma : R →+* S` becomes linear over a common base ring `Q`
whenever the two structural maps from `Q` form a commutative triangle with `sigma`.  Both source
and target are restricted directly to `Q`; no iterated scalar restriction is exposed.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe uQ uR uS uA

namespace ChainDGAlgebra.SemilinearHom

variable {Q : Type uQ} {R : Type uR} {S : Type uS}
variable [CommRing Q] [CommRing R] [CommRing S]
variable {rho : Q →+* R} {tau : Q →+* S} {sigma : R →+* S}
-- The semilinear owner itself allows different carrier universes.  This bundled-hom bridge uses
-- one carrier universe because `ChainDGAlgebra.Hom` currently does so.
variable {A : ChainDGAlgebra.{uR, uA} R} {B : ChainDGAlgebra.{uS, uA} S}

/-- A semilinear homogeneous component becomes linear over a common base ring when the scalar
maps form a commutative triangle. -/
theorem restrictScalarsComponent_smul (f : SemilinearHom sigma A B)
    (h : sigma.comp rho = tau) (n : ℤ) (q : Q)
    (x : (A.restrictScalars rho).X n) :
    f n (q • x) = tau q • f n x := sorry

/-- The homogeneous component of a semilinear map as a linear map over a common base ring. -/
def restrictScalarsLinearMap (f : SemilinearHom sigma A B)
    (h : sigma.comp rho = tau) (n : ℤ) :
    (A.restrictScalars rho).X n →ₗ[Q] (B.restrictScalars tau).X n where
  toFun := f n
  map_add' := f.map_add n
  map_smul' := f.restrictScalarsComponent_smul h n

/-- The homogeneous component of a semilinear map, made linear over a common base ring through a
commutative scalar triangle. -/
def restrictScalarsComponent (f : SemilinearHom sigma A B)
    (h : sigma.comp rho = tau) (n : ℤ) :
    (A.restrictScalars rho).X n ⟶ (B.restrictScalars tau).X n :=
  ModuleCat.ofHom (X := (A.restrictScalars rho).X n)
    (Y := (B.restrictScalars tau).X n) (f.restrictScalarsLinearMap h n)

/-- Restricting the base of a semilinear component does not change its underlying function. -/
@[simp]
theorem restrictScalarsComponent_apply (f : SemilinearHom sigma A B)
    (h : sigma.comp rho = tau) (n : ℤ) (x : (A.restrictScalars rho).X n) :
    f.restrictScalarsComponent h n x = f n x := sorry

/-- The base-restricted homogeneous components commute with the differential. -/
theorem restrictScalarsComponent_comm (f : SemilinearHom sigma A B)
    (h : sigma.comp rho = tau) (i j : ℤ)
    (hij : (ComplexShape.down ℤ).Rel i j) :
    f.restrictScalarsComponent h i ≫ (B.restrictScalars tau).toChainComplex.d i j =
      (A.restrictScalars rho).toChainComplex.d i j ≫
        f.restrictScalarsComponent h j := sorry

/-- The chain map obtained by restricting the source and target of a semilinear chain-DGA map to
a common base ring. -/
def restrictScalarsChainMap (f : SemilinearHom sigma A B)
    (h : sigma.comp rho = tau) :
    (A.restrictScalars rho).toChainComplex ⟶
      (B.restrictScalars tau).toChainComplex where
  f n := f.restrictScalarsComponent h n
  comm' := f.restrictScalarsComponent_comm h

/-- The base-restricted chain map acts degreewise by the original semilinear map. -/
@[simp]
theorem restrictScalarsChainMap_f (f : SemilinearHom sigma A B)
    (h : sigma.comp rho = tau) (n : ℤ) :
    (f.restrictScalarsChainMap h).f n = f.restrictScalarsComponent h n := sorry

/-- The base-restricted chain map preserves the homogeneous unit. -/
theorem restrictScalarsChainMap_one (f : SemilinearHom sigma A B)
    (h : sigma.comp rho = tau) :
    (f.restrictScalarsChainMap h).f 0 (A.restrictScalars rho).one =
      (B.restrictScalars tau).one := sorry

/-- The base-restricted chain map preserves homogeneous multiplication. -/
theorem restrictScalarsChainMap_mul (f : SemilinearHom sigma A B)
    (h : sigma.comp rho = tau) (n m : ℤ)
    (x : (A.restrictScalars rho).X n) (y : (A.restrictScalars rho).X m) :
    (f.restrictScalarsChainMap h).f (n + m)
        ((A.restrictScalars rho).mul n m x y) =
      (B.restrictScalars tau).mul n m
        ((f.restrictScalarsChainMap h).f n x)
        ((f.restrictScalarsChainMap h).f m y) := sorry

/-- Tag 09PQ: restrict a semilinear chain-DGA morphism on both sides to a common base ring through
a commutative scalar triangle. -/
@[stacks 09PQ "restriction of a semilinear chain-DGA morphism to a common base"]
def restrictScalars (f : SemilinearHom sigma A B)
    (h : sigma.comp rho = tau) :
    ChainDGAlgebra.Hom (A.restrictScalars rho) (B.restrictScalars tau) where
  toChainMap := f.restrictScalarsChainMap h
  map_one := f.restrictScalarsChainMap_one h
  map_mul := f.restrictScalarsChainMap_mul h

/-- Restriction to a common base ring preserves the pointwise action of a semilinear chain-DGA
morphism. -/
@[simp]
theorem restrictScalars_apply (f : SemilinearHom sigma A B)
    (h : sigma.comp rho = tau) (n : ℤ) (x : (A.restrictScalars rho).X n) :
    f.restrictScalars h n x = f n x := sorry

/-- Restriction to a common base ring preserves degreewise surjectivity. -/
theorem restrictScalars_surjective (f : SemilinearHom sigma A B)
    (h : sigma.comp rho = tau) (hf : f.Surjective) :
    (f.restrictScalars h).Surjective := sorry

/-- Restriction to a common base ring preserves degreewise injectivity. -/
theorem restrictScalars_injective (f : SemilinearHom sigma A B)
    (h : sigma.comp rho = tau) (hf : f.Injective) :
    (f.restrictScalars h).Injective := sorry

/-- Restriction to a common base ring preserves degreewise bijectivity. -/
theorem restrictScalars_bijective (f : SemilinearHom sigma A B)
    (h : sigma.comp rho = tau) (hf : f.Bijective) :
    (f.restrictScalars h).Bijective := sorry

end ChainDGAlgebra.SemilinearHom
