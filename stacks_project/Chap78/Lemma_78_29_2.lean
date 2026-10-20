/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Separation
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 78.29.2 (1): separatedness of the relation morphism is equivalent to
separatedness of the stabilizer structure morphism and to the stabilizer identity
section being a closed immersion. -/
@[stacks 0455] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.isSeparated_tfae :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B),
      List.TFAE [AlgebraicSpace.Separated G.toPreRelation.hom.left,
        AlgebraicSpace.Separated G.stabilizerMap.left,
        AlgebraicSpace.IsClosedImmersion
          (AlgebraicGeometry.GroupoidAlgebraicSpace.stabilizerOneLift G).left])

/- Lemma 78.29.2 (2): local separatedness of the relation morphism is equivalent
to local separatedness of the stabilizer structure morphism and to the stabilizer
identity section being an immersion. -/
@[stacks 0455] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.locallySeparated_tfae :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B),
      List.TFAE [AlgebraicSpace.LocallySeparated G.toPreRelation.hom.left,
        AlgebraicSpace.LocallySeparated G.stabilizerMap.left,
        AlgebraicSpace.IsImmersion
          (AlgebraicGeometry.GroupoidAlgebraicSpace.stabilizerOneLift G).left])

/- Lemma 78.29.2 (3): quasi-separatedness of the relation morphism is equivalent
to quasi-separatedness of the stabilizer structure morphism and to quasi-compactness
of the stabilizer identity section. -/
@[stacks 0455] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.quasiSeparated_tfae :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B),
      List.TFAE [AlgebraicSpace.QuasiSeparated G.toPreRelation.hom.left,
        AlgebraicSpace.QuasiSeparated G.stabilizerMap.left,
        AlgebraicSpace.QuasiCompact
          (AlgebraicGeometry.GroupoidAlgebraicSpace.stabilizerOneLift G).left])
