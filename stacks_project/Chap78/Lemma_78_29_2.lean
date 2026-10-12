/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap78.Lemma_78_29_1_Diagram

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

/-- Lemma 78.29.2 (1): let `B` be an algebraic space over a scheme `S`, and let
`(U, R, s, t, c)` be a groupoid in algebraic spaces over `B`. Let `G → U` be the
stabilizer group algebraic space. Then `j : R ⟶ U ×_B U`, as
`G.toPreRelation.hom.left`, is separated if and only if `G.stabilizerMap.left`
is separated if and only if `e : U → G`, as `(stabilizerOneLift G).left`, is a
closed immersion. -/
@[stacks 0455]
theorem isSeparated_tfae {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    List.TFAE [AlgebraicSpace.Separated G.toPreRelation.hom.left,
      AlgebraicSpace.Separated G.stabilizerMap.left,
      AlgebraicSpace.IsClosedImmersion (stabilizerOneLift G).left] :=
  sorry

/-- Lemma 78.29.2 (2): let `B` be an algebraic space over a scheme `S`, and let
`(U, R, s, t, c)` be a groupoid in algebraic spaces over `B`. Let `G → U` be the
stabilizer group algebraic space. Then `j : R ⟶ U ×_B U`, as
`G.toPreRelation.hom.left`, is locally separated if and only if
`G.stabilizerMap.left` is locally separated if and only if `e : U → G`, as
`(stabilizerOneLift G).left`, is an immersion. -/
@[stacks 0455]
theorem locallySeparated_tfae {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    List.TFAE [AlgebraicSpace.LocallySeparated G.toPreRelation.hom.left,
      AlgebraicSpace.LocallySeparated G.stabilizerMap.left,
      AlgebraicSpace.IsImmersion (stabilizerOneLift G).left] :=
  sorry

/-- Lemma 78.29.2 (3): let `B` be an algebraic space over a scheme `S`, and let
`(U, R, s, t, c)` be a groupoid in algebraic spaces over `B`. Let `G → U` be the
stabilizer group algebraic space. Then `j : R ⟶ U ×_B U`, as
`G.toPreRelation.hom.left`, is quasi-separated if and only if
`G.stabilizerMap.left` is quasi-separated if and only if `e : U → G`, as
`(stabilizerOneLift G).left`, is quasi-compact. -/
@[stacks 0455]
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
  sorry

/-- The stabilizer structure morphism of a groupoid in algebraic spaces is separated if
and only if its identity section is a closed immersion. -/
theorem isSeparated_stabilizerMap_iff_isClosedImmersion_one
    {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    AlgebraicSpace.Separated G.stabilizerMap.left ↔
      AlgebraicSpace.IsClosedImmersion (stabilizerOneLift G).left :=
  sorry

/-- The relation morphism of a groupoid in algebraic spaces is separated if and only if
the identity section of the stabilizer is a closed immersion. -/
theorem isSeparated_relationMap_iff_isClosedImmersion_one
    {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    AlgebraicSpace.Separated G.toPreRelation.hom.left ↔
      AlgebraicSpace.IsClosedImmersion (stabilizerOneLift G).left :=
  sorry

/-- The relation morphism of a groupoid in algebraic spaces is locally separated if and
only if the stabilizer structure morphism is locally separated. -/
theorem locallySeparated_relationMap_iff_stabilizerMap
    {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    AlgebraicSpace.LocallySeparated G.toPreRelation.hom.left ↔
      AlgebraicSpace.LocallySeparated G.stabilizerMap.left :=
  sorry

/-- The stabilizer structure morphism of a groupoid in algebraic spaces is locally
separated if and only if its identity section is an immersion. -/
theorem locallySeparated_stabilizerMap_iff_isImmersion_one
    {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    AlgebraicSpace.LocallySeparated G.stabilizerMap.left ↔
      AlgebraicSpace.IsImmersion (stabilizerOneLift G).left :=
  sorry

/-- The relation morphism of a groupoid in algebraic spaces is locally separated if and
only if the identity section of the stabilizer is an immersion. -/
theorem locallySeparated_relationMap_iff_isImmersion_one
    {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    AlgebraicSpace.LocallySeparated G.toPreRelation.hom.left ↔
      AlgebraicSpace.IsImmersion (stabilizerOneLift G).left :=
  sorry

/-- The relation morphism of a groupoid in algebraic spaces is quasi-separated if and
only if the stabilizer structure morphism is quasi-separated. -/
theorem quasiSeparated_relationMap_iff_stabilizerMap
    {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    AlgebraicSpace.QuasiSeparated G.toPreRelation.hom.left ↔
      AlgebraicSpace.QuasiSeparated G.stabilizerMap.left :=
  sorry

/-- The stabilizer structure morphism of a groupoid in algebraic spaces is
quasi-separated if and only if its identity section is quasi-compact. -/
theorem quasiSeparated_stabilizerMap_iff_quasiCompact_one
    {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    AlgebraicSpace.QuasiSeparated G.stabilizerMap.left ↔
      AlgebraicSpace.QuasiCompact (stabilizerOneLift G).left :=
  sorry

/-- The relation morphism of a groupoid in algebraic spaces is quasi-separated if and
only if the identity section of the stabilizer is quasi-compact. -/
theorem quasiSeparated_relationMap_iff_quasiCompact_one
    {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    AlgebraicSpace.QuasiSeparated G.toPreRelation.hom.left ↔
      AlgebraicSpace.QuasiCompact (stabilizerOneLift G).left :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
