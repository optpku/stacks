/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.VanishingH1
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiberDegree.Points

/-!
# Cohomology vanishing from affine étale covers

A bound on the point-fibre cardinalities of a surjective étale cover by an affine
scheme bounds the cohomological degrees of quasi-coherent modules on a
quasi-compact absolutely separated algebraic space.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Étale cohomology of a quasi-coherent module on a quasi-compact absolutely
separated algebraic space vanishes in degrees at least a uniform bound on the
point-fibre cardinalities of a surjective étale cover by an affine scheme. -/
@[stacks 072B]
theorem cohomology_isZero_of_fibre_encard_le
    {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    [IsQuasiCompact X] [IsAbsolutelySeparated X] [AlgebraicGeometry.IsAffine U.left]
    (f : ofOver U ⟶ X) [Etale f] [Surjective f]
    (d : ℕ) (hd : ∀ x : Points X, (Points.mapOfOver f ⁻¹' {x}).encard ≤ d)
    (F : X.Modules) [F.IsQuasicoherent] {q : ℕ} (hq : d ≤ q)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})] :
    IsZero (cohomology X F q) :=
  sorry

/-- Étale cohomology of a quasi-coherent module on a quasi-compact absolutely
separated algebraic space vanishes in degrees at least `d` when a surjective
étale cover by an affine scheme has field-valued fibre degrees bounded by `d`. -/
theorem cohomology_isZero_of_degreesOfFibresBoundedBy
    {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    [IsQuasiCompact X] [IsAbsolutelySeparated X] [AlgebraicGeometry.IsAffine U.left]
    (f : ofOver U ⟶ X) [Etale f] [Surjective f]
    (d : ℕ) (hd : degreesOfFibresBoundedBy f d)
    (F : X.Modules) [F.IsQuasicoherent] {q : ℕ} (hq : d ≤ q)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})] :
    IsZero (cohomology X F q) :=
  cohomology_isZero_of_fibre_encard_le f d
    (degreesOfFibresBoundedBy.mapOfOver_fibre_encard_le f hd) F hq

end AlgebraicGeometry.AlgebraicSpace
