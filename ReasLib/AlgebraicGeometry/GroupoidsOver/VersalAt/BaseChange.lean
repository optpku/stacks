/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.YonedaFibreProduct
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteTypePoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
public import ReasLib.AlgebraicGeometry.GroupoidsOver.RimSchlessinger
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property
import Mathlib.Tactic.CrossRefAttribute

/-!
# Smoothness of a base change at a versal point

Pointwise versality implies smoothness of a representing base-change projection
at finite type points over the versal point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- Over a locally Noetherian base, suppose a groupoid fibration satisfies the
Rim-Schlessinger condition and has diagonal representable by algebraic spaces
and locally of finite type. If an object over a locally finite type scheme is
versal at a finite type point, then the algebraic space representing its
Yoneda two-fibre product with an object over another locally finite type scheme
is smooth over that scheme at every finite type point over the versal point. -/
@[stacks 0CXM]
theorem smoothAt_baseChange_of_isVersalAt {S : Scheme.{u}}
    [IsLocallyNoetherian S] {X : GroupoidsOver S} [HasRimSchlessinger X]
    {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU] (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0]
    [IsVersalAt hU x hx u0]
    (h_diag : relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X))
    (h_lft : Groupoids.Hom.has (@AlgebraicSpace.LocallyOfFiniteType S)
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X))
    {V : Scheme.{u}} (hV : V ⟶ S) [LocallyOfFiniteType hV] (y : X.total)
    (hy : X.p.obj y = Over.mk hV) (Z : AlgebraicSpace S)
    (toV : Z ⟶ AlgebraicSpace.ofOver (Over.mk hV))
    (toU : Z ⟶ AlgebraicSpace.ofOver (Over.mk hU))
    (hZ : representsYonedaFibreProduct hU x hx hV y hy Z toV toU)
    (z0 : AlgebraicSpace.Points Z) (hz0 : AlgebraicSpace.IsFiniteTypePoint z0)
    (h_over : AlgebraicSpace.Points.map toU z0 =
      AlgebraicSpace.ofOver.pointsEquiv (Over.mk hU) u0) :
    AlgebraicSpace.SmoothAt toV z0 :=
  sorry

end AlgebraicGeometry.GroupoidsOver
