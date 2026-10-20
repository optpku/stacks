/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Versal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProper.OpennessOfVersality
public import ReasLib.RingTheory.Noetherian.ULift

/-!
# Openness of versality for families of curves

Versality of a family of curves over a Noetherian base spreads from a finite
type point to the finite type points of an open neighbourhood.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces
namespace Curves

/-- A family of curves over a scheme locally of finite type over `specZ` is
versal at every finite type point of some open neighbourhood of any finite
type point at which it is versal. -/
@[stacks 0D59]
theorem opennessOfVersality_specZ {U : Scheme.{u}} (hU : U ⟶ specZ)
    [AlgebraicGeometry.LocallyOfFiniteType hU] (x : Obj specZ)
    (hx : (p specZ).obj x = Over.mk hU) (u0 : U) :
    IsFiniteTypePoint u0 → IsVersalAt hU x hx u0 →
      ∃ U' : Opens U, u0 ∈ U' ∧
        ∀ u : U, u ∈ U' → IsFiniteTypePoint u → IsVersalAt hU x hx u :=
  sorry

/-- A family of curves over a scheme locally of finite type over a Noetherian
base is versal at every finite type point of some open neighbourhood of any
finite type point at which it is versal. -/
@[stacks 0D59]
theorem opennessOfVersality {S : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S] {U : Scheme.{u}}
    (hU : U ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType hU] (x : Obj S)
    (hx : (p S).obj x = Over.mk hU) (u0 : U) :
    IsFiniteTypePoint u0 → IsVersalAt hU x hx u0 →
      ∃ U' : Opens U, u0 ∈ U' ∧
        ∀ u : U, u ∈ U' → IsFiniteTypePoint u → IsVersalAt hU x hx u :=
  sorry

end Curves
end AlgebraicGeometry.AlgebraicSpace.Spaces
