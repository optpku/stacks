/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Constructible
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The image of an étale locally constructible subset under a quasi-compact morphism of
algebraic spaces which is locally of finite presentation is étale locally constructible. -/
@[stacks 0ECX]
theorem IsEtaleLocallyConstructible.image {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [LocallyOfFinitePresentation f] {E : Set (Points X)}
    (hE : IsEtaleLocallyConstructible E) :
    IsEtaleLocallyConstructible (Points.map f '' E) := sorry

end AlgebraicGeometry.AlgebraicSpace
