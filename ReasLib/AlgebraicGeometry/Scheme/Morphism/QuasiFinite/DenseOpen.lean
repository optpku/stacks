/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

/-- A quasi-finite morphism of schemes is finite over a dense open subset of its target. -/
theorem exists_dense_open_isFinite_restrict_of_quasiFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiFinite f] :
    ∃ U : Y.Opens, Dense (U : Set Y) ∧ IsFinite (f ∣_ U) := sorry

end Scheme.Hom
end AlgebraicGeometry
