/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Pushout.AdmissibleSpan.StructureMap
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.RingTheory.Pullback.FiniteType

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan

/-- The canonical structure morphism from the pushout of an admissible span is locally of
finite type over a locally Noetherian base when every object in the span is locally of finite
type over the base. -/
instance instToBaseLocallyOfFiniteType {S : Scheme.{u}} {Z X Y : Over S}
    (i : Z ⟶ X) (j : Z ⟶ Y) [IsAdmissibleSpan i j] [IsLocallyNoetherian S]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] :
    LocallyOfFiniteType (toBase i j) := sorry

end AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan
