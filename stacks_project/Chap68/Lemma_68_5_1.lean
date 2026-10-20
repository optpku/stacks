module

public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap68.Lemma_68_4_5_Fibre
public import stacks_project.Chap68.Lemma_68_5_1_PropertyAlpha
public import stacks_project.Chap68.Lemma_68_12_8_Decent
public import stacks_project.Chap68.Lemma_68_17_4_Relative
public import stacks_project.Chap68.Remark_68_17_10_VeryReasonable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conditions
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

/- Lemma 68.5.1 (1): condition (γ) at every point is equivalent to (α) and
(β) at every point. -/
@[stacks 03JX] #check
  (AlgebraicGeometry.AlgebraicSpace.isDecent_iff_hasPropertyAlpha_and_hasPropertyBeta :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
      IsDecent X ↔ HasPropertyAlpha X ∧ HasPropertyBeta X)

#check (AlgebraicGeometry.AlgebraicSpace.instHasPropertyAlpha_of_isDecent :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X], HasPropertyAlpha X)

#check (AlgebraicGeometry.AlgebraicSpace.instHasPropertyBeta_of_isDecent :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X], HasPropertyBeta X)

#check (AlgebraicGeometry.AlgebraicSpace.instIsDecent_of_hasPropertyAlpha_of_hasPropertyBeta :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [HasPropertyAlpha X] [HasPropertyBeta X],
    IsDecent X)

/- Condition (γ) is the affine étale chart and self-relation finite-fibre test
at every point. -/
#check (AlgebraicGeometry.AlgebraicSpace.isDecent_iff_forallAffineEtaleFiniteAbove :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    IsDecent X ↔ ∀ x : Points X, forallAffineEtaleFiniteAbove X x)

/- Lemma 68.5.1 (2): (δ) implies (γ). -/
@[stacks 03JX] #check (AlgebraicGeometry.AlgebraicSpace.instIsDecent_of_isReasonable :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsReasonable X], IsDecent X)

/- Lemma 68.5.1 (3): (ε) implies (δ). -/
@[stacks 03JX] #check (AlgebraicGeometry.AlgebraicSpace.instIsReasonable_of_isVeryReasonable :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsVeryReasonable X], IsReasonable X)

/- Lemma 68.5.1 (4): (ζ) implies (ε). -/
@[stacks 03JX] #check
  (AlgebraicGeometry.AlgebraicSpace.instIsVeryReasonable_of_isAbsolutelyZariskiLocallyQuasiSeparated :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [IsAbsolutelyZariskiLocallyQuasiSeparated X], IsVeryReasonable X)

/- Lemma 68.5.1 (5): (η) implies (ζ). -/
@[stacks 03JX] #check
  (AlgebraicGeometry.AlgebraicSpace.instIsAbsolutelyZariskiLocallyQuasiSeparated_of_isAbsolutelyQuasiSeparated :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsAbsolutelyQuasiSeparated X],
      IsAbsolutelyZariskiLocallyQuasiSeparated X)

/- Lemma 68.5.1 (6): (θ) implies (ζ). -/
@[stacks 03JX] #check
  (AlgebraicGeometry.AlgebraicSpace.instIsAbsolutelyZariskiLocallyQuasiSeparated_of_isScheme :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsScheme X],
      IsAbsolutelyZariskiLocallyQuasiSeparated X)

end AlgebraicGeometry.AlgebraicSpace
