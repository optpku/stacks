/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProper.Versal

/-!
# Versality of families of curves

A family of curves is versal at a point when its underlying flat, proper,
finitely presented family of algebraic spaces is versal there.
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
  Iff.rfl

end Curves
end AlgebraicGeometry.AlgebraicSpace.Spaces
