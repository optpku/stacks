/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.TopologicalInvariance
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.Characterization

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- For a thickening `i : X ⟶ X'` of algebraic spaces, base change along `i`
induces an equivalence from the spaces-étale site of `X'` to the spaces-étale
site of `X`. -/
instance spacesEtalePullback_isEquivalence_of_isThickening
    {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X') [IsThickening i] :
    (spacesEtalePullback i).IsEquivalence := spacesEtalePullback.isEquivalence i

/-- For a thickening `i : X ⟶ X'` of algebraic spaces, base change along `i`
induces an equivalence from the small étale site of `X'` to the small étale
site of `X`. -/
instance smallEtalePullback.isEquivalence_of_isThickening
    {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X') [IsThickening i]
    (hf : yoneda.relativelyRepresentable i := IsIntegralHom.relativelyRepresentable i) :
    (smallEtalePullback i hf).IsEquivalence := smallEtalePullback.isEquivalence i

end AlgebraicGeometry.AlgebraicSpace
