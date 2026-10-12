/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry

/-- Every affine morphism of schemes is quasi-separated. -/
instance quasiSeparated_of_isAffineHom {S T : Scheme.{u}}
    (h : S ⟶ T) [IsAffineHom h] : QuasiSeparated h :=
  sorry

end AlgebraicGeometry
