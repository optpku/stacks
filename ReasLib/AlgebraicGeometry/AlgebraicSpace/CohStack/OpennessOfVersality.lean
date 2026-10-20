/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.VersalAt
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat

/-!
# Openness of versality for coherent sheaves

Versality of a finitely presented flat module with proper support on the fibres
of a flat morphism of finite presentation is open among finite type points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

/-- For a flat morphism of finite presentation to a locally Noetherian scheme,
versality of a coherent-sheaf object over a locally finite type test scheme at a
finite type point spreads to all finite type points in an open neighbourhood. -/
theorem opennessOfVersality {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    {X : AlgebraicSpace S} (f : X ⟶ ofOver (Over.mk (𝟙 S)))
    [FinitePresentation f] [Flat f] {U : Scheme.{u}} (hU : U ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType hU] (x : Obj f) (hx : (p f).obj x = Over.mk hU)
    (u0 : U) : IsFiniteTypePoint u0 → IsVersalAt f hU x hx u0 →
      ∃ U' : Opens U, u0 ∈ U' ∧
        ∀ u : U, u ∈ U' → IsFiniteTypePoint u → IsVersalAt f hU x hx u :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
