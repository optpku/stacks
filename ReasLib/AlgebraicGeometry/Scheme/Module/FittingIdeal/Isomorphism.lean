/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FittingIdeal

/-!
# Isomorphism invariance of Fitting ideal sheaves

Fitting ideal sheaves of finite-type quasi-coherent scheme modules are invariant under
isomorphism.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

/-- Isomorphic finite-type quasi-coherent scheme modules have equal Fitting ideal sheaves. -/
theorem fittingIdealSheaf_eq_of_iso
    (ℱ ℱ' : S.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent]
    (e : ℱ ≅ ℱ') (i : ℕ) :
    fittingIdealSheaf ℱ i = fittingIdealSheaf ℱ' i := sorry

end AlgebraicGeometry.Scheme
