/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.SeparationDiagram
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact

/-!
# Separation conditions for groupoids in algebraic spaces

The relation morphism of a groupoid in algebraic spaces is separated (resp.
locally separated, resp. quasi-separated) if and only if the stabilizer structure
morphism is, if and only if the identity section of the stabilizer is a closed
immersion (resp. an immersion, resp. quasi-compact).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The relation morphism of a groupoid in algebraic spaces is separated exactly when
its stabilizer structure morphism is separated, equivalently when the stabilizer identity
section is a closed immersion. -/
theorem isSeparated_tfae {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    List.TFAE [AlgebraicSpace.Separated G.toPreRelation.hom.left,
      AlgebraicSpace.Separated G.stabilizerMap.left,
      AlgebraicSpace.IsClosedImmersion (stabilizerOneLift G).left] :=
  sorry

/-- The relation morphism of a groupoid in algebraic spaces is locally separated exactly
when its stabilizer structure morphism is locally separated, equivalently when the stabilizer
identity section is an immersion. -/
theorem locallySeparated_tfae {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    List.TFAE [AlgebraicSpace.LocallySeparated G.toPreRelation.hom.left,
      AlgebraicSpace.LocallySeparated G.stabilizerMap.left,
      AlgebraicSpace.IsImmersion (stabilizerOneLift G).left] :=
  sorry

/-- The relation morphism of a groupoid in algebraic spaces is quasi-separated exactly
when its stabilizer structure morphism is quasi-separated, equivalently when the stabilizer
identity section is quasi-compact. -/
theorem quasiSeparated_tfae {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    List.TFAE [AlgebraicSpace.QuasiSeparated G.toPreRelation.hom.left,
      AlgebraicSpace.QuasiSeparated G.stabilizerMap.left,
      AlgebraicSpace.QuasiCompact (stabilizerOneLift G).left] :=
  sorry

/-- The relation morphism of a groupoid in algebraic spaces is separated if and only if
the stabilizer structure morphism is separated. -/
theorem isSeparated_relationMap_iff_stabilizerMap {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    AlgebraicSpace.Separated G.toPreRelation.hom.left ↔
      AlgebraicSpace.Separated G.stabilizerMap.left :=
  (isSeparated_tfae G).out 0 1

/-- The stabilizer structure morphism of a groupoid in algebraic spaces is separated if
and only if its identity section is a closed immersion. -/
theorem isSeparated_stabilizerMap_iff_isClosedImmersion_one
    {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    AlgebraicSpace.Separated G.stabilizerMap.left ↔
      AlgebraicSpace.IsClosedImmersion (stabilizerOneLift G).left :=
  (isSeparated_tfae G).out 1 2

/-- The relation morphism of a groupoid in algebraic spaces is separated if and only if
the identity section of the stabilizer is a closed immersion. -/
theorem isSeparated_relationMap_iff_isClosedImmersion_one
    {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    AlgebraicSpace.Separated G.toPreRelation.hom.left ↔
      AlgebraicSpace.IsClosedImmersion (stabilizerOneLift G).left :=
  (isSeparated_tfae G).out 0 2

/-- The relation morphism of a groupoid in algebraic spaces is locally separated if and
only if the stabilizer structure morphism is locally separated. -/
theorem locallySeparated_relationMap_iff_stabilizerMap
    {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    AlgebraicSpace.LocallySeparated G.toPreRelation.hom.left ↔
      AlgebraicSpace.LocallySeparated G.stabilizerMap.left :=
  (locallySeparated_tfae G).out 0 1

/-- The stabilizer structure morphism of a groupoid in algebraic spaces is locally
separated if and only if its identity section is an immersion. -/
theorem locallySeparated_stabilizerMap_iff_isImmersion_one
    {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    AlgebraicSpace.LocallySeparated G.stabilizerMap.left ↔
      AlgebraicSpace.IsImmersion (stabilizerOneLift G).left :=
  (locallySeparated_tfae G).out 1 2

/-- The relation morphism of a groupoid in algebraic spaces is locally separated if and
only if the identity section of the stabilizer is an immersion. -/
theorem locallySeparated_relationMap_iff_isImmersion_one
    {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    AlgebraicSpace.LocallySeparated G.toPreRelation.hom.left ↔
      AlgebraicSpace.IsImmersion (stabilizerOneLift G).left :=
  (locallySeparated_tfae G).out 0 2

/-- The relation morphism of a groupoid in algebraic spaces is quasi-separated if and
only if the stabilizer structure morphism is quasi-separated. -/
theorem quasiSeparated_relationMap_iff_stabilizerMap
    {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    AlgebraicSpace.QuasiSeparated G.toPreRelation.hom.left ↔
      AlgebraicSpace.QuasiSeparated G.stabilizerMap.left :=
  (quasiSeparated_tfae G).out 0 1

/-- The stabilizer structure morphism of a groupoid in algebraic spaces is
quasi-separated if and only if its identity section is quasi-compact. -/
theorem quasiSeparated_stabilizerMap_iff_quasiCompact_one
    {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    AlgebraicSpace.QuasiSeparated G.stabilizerMap.left ↔
      AlgebraicSpace.QuasiCompact (stabilizerOneLift G).left :=
  (quasiSeparated_tfae G).out 1 2

/-- The relation morphism of a groupoid in algebraic spaces is quasi-separated if and
only if the identity section of the stabilizer is quasi-compact. -/
theorem quasiSeparated_relationMap_iff_quasiCompact_one
    {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    AlgebraicSpace.QuasiSeparated G.toPreRelation.hom.left ↔
      AlgebraicSpace.QuasiCompact (stabilizerOneLift G).left :=
  (quasiSeparated_tfae G).out 0 2

end AlgebraicGeometry.GroupoidAlgebraicSpace
