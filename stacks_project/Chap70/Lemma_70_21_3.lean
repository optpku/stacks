module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Definition_67_41_1_ValuativeCriterion
public import stacks_project.Chap69.Lemma_69_19_2_DVR
public import stacks_project.Chap70.Lemma_70_21_3_DvrCodimZero

/-!
# Noetherian DVR valuative criterion for properness

A quasi-separated, finite-type morphism of algebraic spaces into a locally
Noetherian target is proper iff it satisfies the valuative criterion, iff every
valuative square has a unique dotted lift, iff unique lifts exist for discrete
valuation rings, iff unique lifts exist for DVR squares whose generic image is a
point of codimension `0`.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Proper

/-- Lemma 70.21.3: for a quasi-separated, finite-type morphism `f : X ⟶ Y` of
algebraic spaces over a scheme `S` with `Y` locally Noetherian, the following are
equivalent: `Proper f`; the valuative criterion of Definition 67.41.1; unique
dotted lifts in every valuative square `Spec(K) ⟶ X` over `Spec(A) ⟶ Y`; the same
unique lifts when `A` is a discrete valuation ring; and the same unique lifts when
`A` is a discrete valuation ring and the image of `Spec(K) ⟶ X` is a point of
codimension `0` on `X`. -/
@[stacks 0H1X]
theorem tfae_valuativeCriterion_dvr_codimZero {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiSeparated f] [FiniteType f] [IsLocallyNoetherian Y] :
    List.TFAE [Proper f, ValuativeCriterion f,
      ∀ sq : ValuativeCommSq f, sq.commSq.HasLift ∧ Subsingleton sq.commSq.LiftStruct,
      ValuativeCriterion.DVR f, ValuativeCriterion.DVR.AtCodimZero f] :=
  sorry

/-- A quasi-separated, finite-type morphism into a locally Noetherian algebraic space
is proper if and only if it satisfies the valuative criterion. -/
theorem iff_valuativeCriterion {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiSeparated f] [FiniteType f] [IsLocallyNoetherian Y] :
    Proper f ↔ ValuativeCriterion f :=
  sorry

/-- A quasi-separated, finite-type morphism into a locally Noetherian algebraic space
is proper if and only if every valuative square has a unique dotted lift. -/
theorem iff_uniqueLift {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiSeparated f] [FiniteType f] [IsLocallyNoetherian Y] :
    Proper f ↔ ∀ sq : ValuativeCommSq f,
      sq.commSq.HasLift ∧ Subsingleton sq.commSq.LiftStruct :=
  sorry

/-- A quasi-separated, finite-type morphism into a locally Noetherian algebraic space
is proper if and only if every DVR valuative square has a unique lift. -/
theorem iff_dvr {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiSeparated f] [FiniteType f] [IsLocallyNoetherian Y] :
    Proper f ↔ ValuativeCriterion.DVR f :=
  sorry

/-- A quasi-separated, finite-type morphism into a locally Noetherian algebraic space
is proper if and only if every DVR valuative square whose generic image has
codimension `0` has a unique lift. -/
theorem iff_dvrAtCodimZero {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiSeparated f] [FiniteType f] [IsLocallyNoetherian Y] :
    Proper f ↔ ValuativeCriterion.DVR.AtCodimZero f :=
  sorry

/-- A quasi-separated, finite-type morphism into a locally Noetherian algebraic space
that satisfies unique DVR lifts at codimension-zero points is proper. -/
instance of_dvrAtCodimZero {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiSeparated f] [FiniteType f] [IsLocallyNoetherian Y]
    [ValuativeCriterion.DVR.AtCodimZero f] : Proper f :=
  sorry

end Proper

end AlgebraicGeometry.AlgebraicSpace
