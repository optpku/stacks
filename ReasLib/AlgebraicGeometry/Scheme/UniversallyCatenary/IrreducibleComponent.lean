/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.IrreducibleComponent

@[expose] public section

namespace AlgebraicGeometry

universe u

/-- A locally Noetherian scheme is universally catenary if and only if the reduced induced
subscheme supported on each irreducible component is universally catenary. -/
theorem universallyCatenary_iff_forall_irreducibleComponent
    (S : Scheme.{u}) [IsLocallyNoetherian S] :
    UniversallyCatenary S ↔
      ∀ Z : irreducibleComponents S, UniversallyCatenary (S.irreducibleComponentSubscheme Z) :=
  sorry

end AlgebraicGeometry
