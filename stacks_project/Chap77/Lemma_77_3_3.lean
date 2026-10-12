/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap77.Lemma_77_3_3_Purity

/-!
# Quasi-finite pointed base change of purity on algebraic spaces

Purity of a finite type quasi-coherent module above a selected point is preserved
by a pointed base change that is quasi-finite at the source point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules
namespace IsPureAlong

/-- Lemma 77.3.3: In Situation 77.2.1, let `(Y', y') ⟶ (Y, y)` be a morphism of
pointed algebraic spaces. If `Y' ⟶ Y` is quasi-finite at `y'` and `F` is pure
above `y`, then the pullback of `F` to `X ×_Y Y'` is pure above `y'`. -/
@[stacks 0CVF]
theorem pullback_of_quasiFiniteAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [FiniteType f] [Decent f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (y : |Y|) {Y' : AlgebraicSpace S}
    (g : Y' ⟶ Y) (y' : |Y'|) (hpoint : Points.map g y' = y)
    (hquasi : FiniteType.QuasiFiniteAt g y') (hpure : IsPureAlong F f y) :
    IsPureAlong ((pullback (Limits.pullback.fst f g)).obj F)
      (Limits.pullback.snd f g) y' :=
  sorry

end IsPureAlong
end AlgebraicGeometry.AlgebraicSpace.Modules
