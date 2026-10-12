/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.InvariantBaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Action.Pullback
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits
open AlgebraicGeometry.AlgebraicSpace.PreRelation
open AlgebraicGeometry.GroupoidAlgebraicSpace
open AlgebraicGeometry.GroupAlgebraicSpace

universe u

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {U X X' : Over B}
variable (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ) (f : X' ⟶ X)

/- Lemma 83.3.3 (1): if φ : U ⟶ X is R-invariant for a pre-relation
j = (t, s) : R ⟶ U ×_B U and f : X' ⟶ X is any morphism of algebraic spaces over B,
then U' = X' ×_X U and R' = X' ×_X R yield a pre-relation j' : R' ⟶ U' ×_B U'. -/
@[stacks 048G] #check (AlgebraicGeometry.AlgebraicSpace.PreRelation.baseChange P hφ f :
  PreRelation (pullback φ f))

variable [Mono P.hom]

/- Lemma 83.3.3 (2): if j is a relation, then j' is a relation. -/
@[stacks 048G] #check (AlgebraicGeometry.AlgebraicSpace.PreRelation.monoHom_baseChange P hφ f :
  Mono (P.baseChange hφ f).hom)

variable (hP : P.IsPreEquivalence)

/- Lemma 83.3.3 (3): if j is a pre-equivalence relation, then j' is a pre-equivalence
relation. -/
@[stacks 048G] #check (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsPreEquivalence.baseChange
  hP hφ f : (P.baseChange hφ f).IsPreEquivalence)

variable [IsEquivalenceRelation P.t P.s]

/- Lemma 83.3.3 (4): if j is an equivalence relation, then j' is an equivalence
relation. -/
@[stacks 048G] #check (AlgebraicGeometry.AlgebraicSpace.PreRelation.isEquivalenceRelation_baseChange
  P hφ f :
  IsEquivalenceRelation (P.baseChange hφ f).t (P.baseChange hφ f).s)

variable (G : GroupoidAlgebraicSpace B) {ψ : G.U ⟶ X}
variable (hψ : G.toPreRelation.IsInvariantHom ψ)

/- Lemma 83.3.3 (5): if j comes from a groupoid in algebraic spaces (U, R, s, t, c)
over B, then (U, R, s, t, c) is a groupoid in algebraic spaces over X. -/
@[stacks 048G] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.over G ψ hψ :
  GroupoidAlgebraicSpace X.left)

/- Lemma 83.3.3 (6): j' comes from the base change (U', R', s', t', c') of this
groupoid to X', see Groupoids in Spaces, Lemma 78.11.6; after transport along
X' ⟶ B, its underlying pre-relation is canonically isomorphic to the invariant
base change. -/
@[stacks 048G] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.toPreRelation_over_baseChange
  G ψ hψ f :
  (Over.map
      (prod.map (changeBase_over_UIso G ψ hψ f).hom
        (changeBase_over_UIso G ψ hψ f).hom)).obj
    (changeBase X'.hom (GroupoidAlgebraicSpace.baseChange f.left (over G ψ hψ))).toPreRelation ≅
    G.toPreRelation.baseChange hψ f)

variable (H : GroupAlgebraicSpace B) (Xg : Action H)
variable {χ : Xg.X ⟶ X} (hχ : (ofAction H Xg).toPreRelation.IsInvariantHom χ)

/- Lemma 83.3.3 (7): if j comes from the action of a group algebraic space G/B on U
as in Groupoids in Spaces, Lemma 78.15.1, then j' comes from the induced action of G
on U'. -/
@[stacks 048G] #check (AlgebraicGeometry.GroupAlgebraicSpace.Action.pullback H Xg χ hχ f :
  Action H)

/- Lemma 83.3.3 (8): the underlying pre-relation of the induced action is canonically
isomorphic to the invariant base change of the original action groupoid. -/
@[stacks 048G] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.toPreRelation_pullback
  H Xg χ hχ f :
  (ofAction H (Action.pullback H Xg χ hχ f)).toPreRelation ≅
    (ofAction H Xg).toPreRelation.baseChange hχ f)
