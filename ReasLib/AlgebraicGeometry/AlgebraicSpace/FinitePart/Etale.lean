/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.Point
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.BaseChange

/-!
# Étale criterion for the finite-part functor
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FinitePart

/-- For a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`, an
étale morphism `a : U ⟶ Y` from a scheme and an open subspace of `U ×_Y X`
finite over `U` induce a representable étale morphism `U ⟶ (X/Y)_fin`. -/
theorem hom_etale {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {U : Over S} (a : ofOver U ⟶ Y) [AlgebraicSpace.Etale a]
    (Z : OpenSubspace (pullback a f))
    (hZ : IsFinite (Z.ι ≫ pullback.fst a f)) :
    (over (@AlgebraicGeometry.Etale : MorphismProperty Scheme.{u})).presheaf
      (SubspacePoint.hom (SubspacePoint.of a Z hZ)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FinitePart
