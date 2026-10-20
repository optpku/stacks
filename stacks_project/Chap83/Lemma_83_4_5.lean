module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.ReducedQuotient
public import stacks_project.Chap67.Lemma_67_48_6_Reduced
public import stacks_project.Chap83.Example_83_4_3_Categories

/-!
# Reducedness of categorical quotients
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 83.4.5 (1): in the situation of Definition 83.4.1, if `φ : U ⟶ X` is a
categorical quotient and `U` is reduced, then `X` is reduced. -/
@[stacks 049W] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsCategoricalQuotient.isReduced :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsCategoricalQuotient φ)
    [IsReduced U.left], IsReduced X.left)

/- Lemma 83.4.5 (2): if `φ : U ⟶ X` is a categorical quotient in the category of
separated algebraic spaces over a separated base `B` and `U` is reduced, then `X`
is reduced. -/
@[stacks 049W] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsCategoricalQuotientInSeparated.isReduced :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} [IsAbsolutelySeparated B]
    {U X : Over B} (P : PreRelation U) {φ : U ⟶ X}
    (hφ : P.IsCategoricalQuotientInSeparated φ) [IsReduced U.left], IsReduced X.left)

/- Lemma 83.4.5 (3): if `φ : U ⟶ X` is a categorical quotient in the category of
quasi-separated algebraic spaces over a quasi-separated base `B` and `U` is reduced,
then `X` is reduced. -/
@[stacks 049W] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsCategoricalQuotientInQuasiSeparated.isReduced :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    [IsAbsolutelyQuasiSeparated B] {U X : Over B} (P : PreRelation U) {φ : U ⟶ X}
    (hφ : P.IsCategoricalQuotientInQuasiSeparated φ) [IsReduced U.left], IsReduced X.left)

/- Lemma 83.4.5 (4): if `φ : U ⟶ X` is a categorical quotient in the category of
locally separated algebraic spaces over a locally separated base `B` and `U` is
reduced, then `X` is reduced. -/
@[stacks 049W] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsCategoricalQuotientInLocallySeparated.isReduced :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    [IsAbsolutelyLocallySeparated B] {U X : Over B} (P : PreRelation U)
    {φ : U ⟶ X} (hφ : P.IsCategoricalQuotientInLocallySeparated φ)
    [IsReduced U.left], IsReduced X.left)

/- Lemma 83.4.5 (5): if `φ : U ⟶ X` is a categorical quotient in the category of
decent algebraic spaces over a decent base `B` and `U` is reduced, then `X` is
reduced. -/
@[stacks 049W] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsCategoricalQuotientInDecent.isReduced :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} [IsDecent B]
    {U X : Over B} (P : PreRelation U) {φ : U ⟶ X}
    (hφ : P.IsCategoricalQuotientInDecent φ) [IsReduced U.left], IsReduced X.left)

/- Lemma 83.4.5 (6): if `φ : U ⟶ X` is a categorical quotient in the category of
schemes over `S` and `U` is reduced, then `X` is reduced. -/
@[stacks 049W] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsCategoricalQuotientInSchemes.isReduced :
    ∀ {S : Scheme.{u}} {U X : Over (ofOver (Over.mk (𝟙 S)))}
    (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsCategoricalQuotientInSchemes φ)
    [IsReduced U.left], IsReduced X.left)
