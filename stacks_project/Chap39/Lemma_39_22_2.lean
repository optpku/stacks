/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Separation
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 39.22.2: the relation morphism of a groupoid scheme is separated exactly when its
stabilizer structure morphism is separated. -/
@[stacks 02YI] #check
  (AlgebraicGeometry.GroupoidScheme.isSeparated_relationMap_iff_stabilizerMap :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S),
      AlgebraicGeometry.IsSeparated G.toPreRelation.hom.left ↔
        AlgebraicGeometry.IsSeparated G.stabilizerMap.left)

#check
  (AlgebraicGeometry.GroupoidScheme.isSeparated_stabilizerMap_iff_isClosedImmersion_one :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S),
      AlgebraicGeometry.IsSeparated G.stabilizerMap.left ↔
        AlgebraicGeometry.IsClosedImmersion
          (AlgebraicGeometry.GroupoidScheme.stabilizerOneLift G).left)

#check
  (AlgebraicGeometry.GroupoidScheme.quasiSeparated_relationMap_iff_stabilizerMap :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S),
      AlgebraicGeometry.QuasiSeparated G.toPreRelation.hom.left ↔
        AlgebraicGeometry.QuasiSeparated G.stabilizerMap.left)

#check
  (AlgebraicGeometry.GroupoidScheme.quasiSeparated_stabilizerMap_iff_quasiCompact_one :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S),
      AlgebraicGeometry.QuasiSeparated G.stabilizerMap.left ↔
        AlgebraicGeometry.QuasiCompact
          (AlgebraicGeometry.GroupoidScheme.stabilizerOneLift G).left)
