/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap99.Lemma_99_13_9_Versal
public import stacks_project.Chap99.Situation_99_15_1_Category

/-!
# Versality of `Curves` at finite type points

An object of `Curves.Obj S` is versal at a finite type point when the
underlying object of `Spaces'_{fp, flat, proper}` is versal there, along the
fully faithful inclusion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces
namespace Curves

/-- An object `x` of `Curves` over `U` is versal at a point `u0` of `U` when
the image of `x` in `Spaces'_{fp, flat, proper}` is versal at `u0`. -/
def IsVersalAt {S : Scheme.{u}} {U : Scheme.{u}} (hU : U ⟶ S)
    [AlgebraicGeometry.IsLocallyNoetherian S]
    [AlgebraicGeometry.LocallyOfFiniteType hU] (x : Obj S)
    (hx : (p S).obj x = Over.mk hU) (u0 : U) : Prop :=
  FpFlatProperGroupoids.IsVersalAt hU x.obj hx u0

/-- Versality of a family of curves at `u0` is versality of the underlying
object of `Spaces'_{fp, flat, proper}`. -/
theorem isVersalAt_iff {S : Scheme.{u}} {U : Scheme.{u}} (hU : U ⟶ S)
    [AlgebraicGeometry.IsLocallyNoetherian S]
    [AlgebraicGeometry.LocallyOfFiniteType hU] (x : Obj S)
    (hx : (p S).obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0] :
    IsVersalAt hU x hx u0 ↔ FpFlatProperGroupoids.IsVersalAt hU x.obj hx u0 :=
  sorry

end Curves
end AlgebraicGeometry.AlgebraicSpace.Spaces
