/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap68.Lemma_68_4_5_Fibre
public import stacks_project.Chap68.Lemma_68_5_1_PropertyAlpha
public import stacks_project.Chap68.Lemma_68_12_8_Decent
public import stacks_project.Chap68.Lemma_68_17_4_Relative
public import stacks_project.Chap68.Remark_68_17_10_VeryReasonable
import StacksCheckRecall

/-!
# Implications among bounded-fibre and separation conditions

Conditions (α)–(θ) on an algebraic space form the implication diamond of
Lemma 68.5.1. Condition (ι), being a quasi-separated scheme, is the pair
`IsScheme` and `IsAbsolutelyQuasiSeparated`; the arrows (ι) ⇒ (θ) and
(ι) ⇒ (η) are the corresponding projections and are not restated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.5.1 (1): let `S` be a scheme and `X` an algebraic space over `S`.
Condition (γ), that the equivalent conditions of Lemma 68.4.5 hold at every
point of `|X|`, is equivalent to the conjunction of (α) and (β), that the
equivalent conditions of Lemmas 68.4.2 and 68.4.3 hold at every point. -/
@[stacks 03JX]
theorem isDecent_iff_hasPropertyAlpha_and_hasPropertyBeta {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    IsDecent X ↔ HasPropertyAlpha X ∧ HasPropertyBeta X :=
  sorry

/-- A decent algebraic space has property (α). -/
instance instHasPropertyAlpha_of_isDecent {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsDecent X] : HasPropertyAlpha X :=
  sorry

/-- A decent algebraic space has property (β). -/
instance instHasPropertyBeta_of_isDecent {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsDecent X] : HasPropertyBeta X :=
  sorry

/-- Properties (α) and (β) together yield a decent algebraic space. -/
instance instIsDecent_of_hasPropertyAlpha_of_hasPropertyBeta
    {S : Scheme.{u}} (X : AlgebraicSpace S) [HasPropertyAlpha X] [HasPropertyBeta X] :
    IsDecent X :=
  sorry

/-- Decency is equivalent to the equivalent conditions of Lemma 68.4.5 at every
point of `|X|`. -/
theorem isDecent_iff_forallAffineEtaleFiniteAbove {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    IsDecent X ↔ ∀ x : Points X, forallAffineEtaleFiniteAbove X x :=
  sorry

/-- Lemma 68.5.1 (2): if the equivalent conditions of Lemma 68.4.6 hold, then
the equivalent conditions of Lemma 68.4.5 hold at every point of `|X|`. -/
@[stacks 03JX, instance 900]
instance instIsDecent_of_isReasonable {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsReasonable X] : IsDecent X :=
  sorry

/-- Lemma 68.5.1 (3): if the equivalent conditions of Lemma 68.4.7 hold, then
the equivalent conditions of Lemma 68.4.6 hold. -/
@[stacks 03JX, instance 900]
instance instIsReasonable_of_isVeryReasonable {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsVeryReasonable X] : IsReasonable X :=
  sorry

/-- Lemma 68.5.1 (4): if `X` is Zariski locally quasi-separated, then the
equivalent conditions of Lemma 68.4.7 hold. -/
@[stacks 03JX, instance 900]
instance instIsVeryReasonable_of_isAbsolutelyZariskiLocallyQuasiSeparated
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsAbsolutelyZariskiLocallyQuasiSeparated X] : IsVeryReasonable X :=
  sorry

/- Lemma 68.5.1 (5): if `X` is quasi-separated, then `X` is Zariski locally
quasi-separated. -/
@[stacks 03JX] #check AlgebraicGeometry.AlgebraicSpace.instIsAbsolutelyZariskiLocallyQuasiSeparated_of_isAbsolutelyQuasiSeparated

/-- Lemma 68.5.1 (6): if `X` is representable, i.e. a scheme, then `X` is
Zariski locally quasi-separated. -/
@[stacks 03JX, instance 900]
instance instIsAbsolutelyZariskiLocallyQuasiSeparated_of_isScheme
    {S : Scheme.{u}} (X : AlgebraicSpace S) [IsScheme X] :
    IsAbsolutelyZariskiLocallyQuasiSeparated X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
