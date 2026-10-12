/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.Galois.Cohomology.Units
public import ReasLib.Algebra.CentralSimple.BrauerGroup.Group
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Action.ModuleCat

namespace GaloisCohomology

/-- If every finite extension of a field has trivial Brauer group, then continuous Galois
cohomology with any torsion discrete integral module vanishes in degrees at least two. -/
theorem torsionCohomologyIsZeroOfFiniteBrauer
    (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (hBr : ∀ (K' : Type u) [Field K'] [Algebra K K'] [FiniteDimensional K K'],
      Subsingleton (Br(K')))
    (M : DiscreteModuleCat ℤ (Gal(Ksep/K))) (hM : Module.IsTorsion ℤ M.obj.V)
    (q : ℕ) (hq : 2 ≤ q) :
    IsZero (DiscreteModuleCat.continuousCohomology (Gal(Ksep/K)) M q) := sorry

/-- If every finite extension of a field has trivial Brauer group, then continuous Galois
cohomology with separable-closure units as coefficients vanishes in every positive degree. -/
theorem unitsCohomologyIsZeroOfFiniteBrauer
    (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (hBr : ∀ (K' : Type u) [Field K'] [Algebra K K'] [FiniteDimensional K K'],
      Subsingleton (Br(K')))
    (q : ℕ) (hq : 1 ≤ q) :
    IsZero
      (DiscreteModuleCat.continuousCohomology (Gal(Ksep/K)) (unitsModule K Ksep) q) := sorry

end GaloisCohomology

end
