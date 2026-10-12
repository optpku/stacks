/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap39.Lemma_39_13_4_Groupoid
public import stacks_project.Chap39.«39_13_5_1_Pullback»

/-!
# Comparison of the two groupoid-scheme interfaces

This module regards a `Scheme.Groupoid` as the older `GroupoidScheme` interface and reuses the
canonical pullback comparison there.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Groupoid

/-- Regard a diagrammatic groupoid scheme as a pointwise `GroupoidScheme`. -/
def toGroupoidScheme {S : Scheme.{u}} (G : Groupoid S) :
    AlgebraicGeometry.GroupoidScheme S where
  U := G.U
  R := G.R
  s := G.s
  t := G.t
  c := G.c
  e := G.e
  i := G.i
  comp_source := G.comp_source
  comp_target := G.comp_target
  identity_source := G.identity_source
  identity_target := G.identity_target
  inverse_source := G.inverse_source
  inverse_target := G.inverse_target
  associativity := G.associativity
  right_identity := G.right_identity
  left_identity := G.left_identity
  inverse_comp := G.inverse_comp
  comp_inverse := G.comp_inverse

/-- The comparison preserves the object scheme. -/
theorem toGroupoidScheme_U {S : Scheme.{u}} (G : Groupoid S) :
    G.toGroupoidScheme.U = G.U := rfl

/-- The comparison preserves the arrow scheme. -/
theorem toGroupoidScheme_R {S : Scheme.{u}} (G : Groupoid S) :
    G.toGroupoidScheme.R = G.R := rfl

/-- The comparison preserves the source map. -/
theorem toGroupoidScheme_s {S : Scheme.{u}} (G : Groupoid S) :
    G.toGroupoidScheme.s = G.s := rfl

/-- The comparison preserves the target map. -/
theorem toGroupoidScheme_t {S : Scheme.{u}} (G : Groupoid S) :
    G.toGroupoidScheme.t = G.t := rfl

/-- The map `(pr₀, c ∘ (i, 1))` from common-target pairs to composable pairs. -/
abbrev targetComparison {S : Scheme.{u}} (G : Groupoid S) :
    pullback G.t G.t ⟶ pullback G.s G.t :=
  G.toGroupoidScheme.targetComparison

/-- The inverse comparison sends a composable pair to its first arrow and its composite. -/
abbrev targetComparisonInv {S : Scheme.{u}} (G : Groupoid S) :
    pullback G.s G.t ⟶ pullback G.t G.t :=
  G.toGroupoidScheme.targetComparisonInv

/-- The canonical isomorphism from common-target pairs to composable pairs. -/
abbrev targetComparisonIso {S : Scheme.{u}} (G : Groupoid S) :
    pullback G.t G.t ≅ pullback G.s G.t :=
  G.toGroupoidScheme.targetComparisonIso

/-- The forward map of `targetComparisonIso` is `(pr₀, c ∘ (i, 1))`. -/
theorem targetComparisonIso_hom {S : Scheme.{u}} (G : Groupoid S) :
    G.targetComparisonIso.hom = G.targetComparison := rfl

/-- The inverse map of `targetComparisonIso` is `(pr₀, c)`. -/
theorem targetComparisonIso_inv {S : Scheme.{u}} (G : Groupoid S) :
    G.targetComparisonIso.inv = G.targetComparisonInv := rfl

/-- The second projection of the inverse target comparison is composition. -/
theorem targetComparisonInv_snd {S : Scheme.{u}} (G : Groupoid S) :
    G.targetComparisonInv ≫ pullback.snd G.t G.t = G.c :=
  AlgebraicGeometry.GroupoidScheme.targetComparisonInv_snd G.toGroupoidScheme

end AlgebraicGeometry.Scheme.Groupoid
