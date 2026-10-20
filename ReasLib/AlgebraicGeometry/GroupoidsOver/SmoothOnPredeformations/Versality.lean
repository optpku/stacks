/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.VersalAt
public import ReasLib.AlgebraicGeometry.GroupoidsOver.RimSchlessinger
public import ReasLib.AlgebraicGeometry.GroupoidsOver.SmoothOnPredeformations

/-!
# Versality at finite type points and smoothness on predeformations

Pointwise versality at finite type points implies smoothness on predeformations
for the associated 2-Yoneda morphism under the Rim-Schlessinger condition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- Over a locally Noetherian base, an object of a category fibred in groupoids
satisfying the Rim-Schlessinger condition, over a locally finite type scheme and
versal at every finite type point, induces a 2-Yoneda morphism smooth on
predeformations. -/
theorem IsSmoothOnPredeformations.of_isVersalAt_finiteTypePoints
    {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    [HasRimSchlessinger X] {U : Scheme.{u}} (hU : U ⟶ S)
    [LocallyOfFiniteType hU] (x : X.total) (hx : X.p.obj x = Over.mk hU)
    (h_versal : ∀ u : U, IsFiniteTypePoint u → IsVersalAt hU x hx u) :
    IsSmoothOnPredeformations (yonedaOfObject hU x hx) :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
