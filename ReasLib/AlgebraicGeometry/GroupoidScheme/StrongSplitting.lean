/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.StrongSplitting

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The arrow points of a groupoid scheme whose source and target are a given object point. -/
def loopPoints {S : Scheme.{u}} (G : GroupoidScheme S) (point : G.U.left) : Set G.R.left :=
  Scheme.Hom.commonFiberPoints G.s.left G.t.left point

/-- An arrow point is a loop at an object point exactly when both endpoints equal that point. -/
theorem mem_loopPoints {S : Scheme.{u}} (G : GroupoidScheme S) (point : G.U.left)
    (arrow : G.R.left) :
    arrow ∈ loopPoints G point ↔ G.s.left arrow = point ∧ G.t.left arrow = point := sorry

/-- A pointed groupoid scheme satisfies strong-splitting hypotheses when its source and target
are separated and locally of finite type, its loop-point set is finite, and its source is
finite-type quasi-finite at every loop point. -/
abbrev StrongSplitting {S : Scheme.{u}} (G : GroupoidScheme S) (point : G.U.left) : Prop :=
  Scheme.Hom.StrongSplittingAt G.s.left G.t.left point

namespace StrongSplitting

/-- Separated, locally finite type source and target maps, a finite loop-point set, and source
finite-type quasi-finiteness at its members give strong-splitting hypotheses. -/
theorem of {S : Scheme.{u}} (G : GroupoidScheme S) (point : G.U.left)
    [IsSeparated G.s.left] [IsSeparated G.t.left]
    [LocallyOfFiniteType G.s.left] [LocallyOfFiniteType G.t.left]
    (hfin : (loopPoints G point).Finite)
    (hqf : ∀ arrow ∈ loopPoints G point, Scheme.Hom.FiniteType.QuasiFiniteAt G.s.left arrow) :
    StrongSplitting G point :=
  Scheme.Hom.StrongSplittingAt.of G.s.left G.t.left point hfin hqf

/-- Strong-splitting hypotheses are equivalent to separatedness and local finite type of both
maps, finiteness of the loop-point set, and source finite-type quasi-finiteness on that set. -/
theorem iff {S : Scheme.{u}} (G : GroupoidScheme S) (point : G.U.left) :
    StrongSplitting G point ↔
      IsSeparated G.s.left ∧ IsSeparated G.t.left ∧
        LocallyOfFiniteType G.s.left ∧ LocallyOfFiniteType G.t.left ∧
          (loopPoints G point).Finite ∧
            ∀ arrow ∈ loopPoints G point,
              Scheme.Hom.FiniteType.QuasiFiniteAt G.s.left arrow :=
  Scheme.Hom.StrongSplittingAt.iff G.s.left G.t.left point

/-- For separated, locally finite type source and target maps, a finite source fibre implies
strong-splitting hypotheses at the chosen object point. -/
theorem of_finite_sourceFiber {S : Scheme.{u}} (G : GroupoidScheme S) (point : G.U.left)
    [IsSeparated G.s.left] [IsSeparated G.t.left]
    [LocallyOfFiniteType G.s.left] [LocallyOfFiniteType G.t.left]
    (hfin : Set.Finite (G.s.left ⁻¹' ({point} : Set G.U.left))) :
    StrongSplitting G point :=
  Scheme.Hom.StrongSplittingAt.ofFiniteSourceFiber G.s.left G.t.left point hfin

end StrongSplitting

end AlgebraicGeometry.GroupoidScheme
