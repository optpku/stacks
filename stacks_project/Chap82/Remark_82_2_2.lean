/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Sober
import StacksCheckRecall

/-!
# Sobriety of points of a good algebraic space

In the setup of Situation 82.2.1, a good algebraic space over a quasi-separated
base has sober space of points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Remark 82.2.2: in Situation 82.2.1, a good algebraic space `X / B` has a sober
space of points. The setup assumes a quasi-separated, locally Noetherian,
universally catenary base with a dimension function, and a quasi-separated,
locally finite type structure morphism. Only the displayed separation hypotheses
are needed for sobriety, which means both `T0Space` and `QuasiSober`. -/
@[stacks 0EDU]
#check (AlgebraicGeometry.AlgebraicSpace.points_sober_of_quasiSeparated :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f], T0Space (Points X) ∧ QuasiSober (Points X))

/- Every irreducible closed subset of the space of points has a unique generic
point, in particular for a good algebraic space in Situation 82.2.1. -/
#check (AlgebraicGeometry.AlgebraicSpace.existsUnique_isGenericPoint_of_quasiSeparated :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] {T : Set (Points X)}
    (hT_irred : IsIrreducible T) (hT_closed : IsClosed T),
    ∃! x : Points X, IsGenericPoint x T)

end AlgebraicGeometry.AlgebraicSpace
