/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Variety

universe u

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry
namespace Scheme.Hom

/-- The degree of a closed point of a variety over `k` is the residue degree of its structure morphism. -/
noncomputable def closedPointDegree {k : Type u} [Field k] (X : SchemeOverField k) [Variety X]
    (x : closedPoints X.left) : ℕ := X.hom.residueDegree x.1

end Scheme.Hom
end AlgebraicGeometry
