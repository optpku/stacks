/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.ApproximationByPerfectComplexes
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ElementaryDistinguishedSquare
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.HasApproximationByPerfectComplexes

/-- For an elementary distinguished square of algebraic spaces over a scheme,
approximation by perfect complexes on the quasi-compact open member implies
approximation by perfect complexes on the whole space if the étale member is
affine and its pullback to the open member is quasi-compact. -/
theorem of_isElementaryDistinguishedSquare
    {S : Scheme.{u}} {U V X : AlgebraicSpace S} (j : U ⟶ X) (f : V ⟶ X)
    [IsElementaryDistinguishedSquare j f] [IsQuasiCompact U] [IsAffine V]
    [IsQuasiCompact (pullback j f)] (hU : HasApproximationByPerfectComplexes U) :
    HasApproximationByPerfectComplexes X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.HasApproximationByPerfectComplexes
