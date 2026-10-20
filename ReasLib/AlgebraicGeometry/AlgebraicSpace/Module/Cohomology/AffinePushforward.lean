/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.VanishingH1
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HigherDirectImage.Affine
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.Leray.Degeneration

/-!
# Cohomology under affine pushforward

Étale cohomology of a quasi-coherent module is preserved by pushforward along an affine
morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Étale cohomology of a quasi-coherent module on an algebraic space is isomorphic to the
cohomology of its pushforward along an affine morphism in every natural-number degree. -/
@[stacks 0D2U]
theorem cohomology_iso_pushforward_of_affine
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Affine f]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u})]
    (F : X.Modules) [F.IsQuasicoherent] (i : ℕ) :
    IsIsomorphic (cohomology X F i) (cohomology Y ((Modules.pushforward f).obj F) i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
