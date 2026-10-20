/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.SeparationDiagram
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.TargetLocus
public import ReasLib.CategoryTheory.Subobject.Invariant

/-!
# Invariant target loci in groupoids in algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- If the source and target maps of a groupoid in algebraic spaces are covers for
the fppf, étale, smooth, or syntomic topology, the maximal target-open locus where
the source map has a property local on the target for that topology is invariant. -/
theorem isOpenInvariant_targetLocus_source {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (P : MorphismProperty (AlgebraicSpace S))
    {K : Precoverage (AlgebraicSpace S)} [P.IsLocalAtTarget K]
    (hτ : AlgebraicSpace.isFppfToEtalePrecoverage K)
    (hs : Presieve.singleton G.s.left ∈ K.coverings G.U.left)
    (ht : Presieve.singleton G.t.left ∈ K.coverings G.U.left) :
    CategoryTheory.Morphism.IsForwardInvariant G.s.left G.t.left
      (AlgebraicSpace.targetLocus P G.s.left).ι :=
  sorry

/-- If the source and target maps of a groupoid in algebraic spaces are covers for
the fppf, étale, smooth, or syntomic topology, the maximal target-open locus where
the stabilizer structure morphism has a property local on the target for that
topology is invariant. -/
theorem isOpenInvariant_targetLocus_stabilizerMap {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (P : MorphismProperty (AlgebraicSpace S))
    {K : Precoverage (AlgebraicSpace S)} [P.IsLocalAtTarget K]
    (hτ : AlgebraicSpace.isFppfToEtalePrecoverage K)
    (hs : Presieve.singleton G.s.left ∈ K.coverings G.U.left)
    (ht : Presieve.singleton G.t.left ∈ K.coverings G.U.left) :
    CategoryTheory.Morphism.IsForwardInvariant G.s.left G.t.left
      (AlgebraicSpace.targetLocus P G.stabilizerMap.left).ι :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
