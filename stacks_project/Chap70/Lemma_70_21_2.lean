module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Definition_67_41_1_ValuativeCriterion
public import stacks_project.Chap69.Lemma_69_19_1_DVR
public import stacks_project.Chap70.Lemma_70_21_2_DvrUniqueness

/-!
# Noetherian DVR valuative criterion for separatedness

A quasi-separated, locally finite-type morphism of algebraic spaces into a locally
Noetherian target is separated iff it satisfies uniqueness in the valuative
criterion, iff uniqueness holds for discrete valuation rings, iff uniqueness holds
for DVR squares whose generic image is a point of codimension `0`.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Separated

/-- Lemma 70.21.2: for a quasi-separated, locally finite-type morphism `f : X ⟶ Y` of
algebraic spaces over a scheme `S` with `Y` locally Noetherian, the following are
equivalent: `Separated f`; uniqueness of dotted lifts in every valuative square
`Spec(K) ⟶ X` over `Spec(A) ⟶ Y`; the same uniqueness when `A` is a discrete
valuation ring; and the same uniqueness when `A` is a discrete valuation ring and
the image of `Spec(K) ⟶ X` is a point of codimension `0` on `X`. -/
@[stacks 0H1W]
theorem tfae_valuativeCriterion_dvr_codimZero {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiSeparated f] [LocallyOfFiniteType f] [IsLocallyNoetherian Y] :
    List.TFAE [Separated f, ValuativeCriterion.Uniqueness f,
      ValuativeCriterion.DVR.Uniqueness f,
      ValuativeCriterion.DVR.UniquenessAtCodimZero f] :=
  sorry

/-- A quasi-separated, locally finite-type morphism into a locally Noetherian algebraic
space is separated if and only if it satisfies uniqueness in the valuative criterion. -/
theorem iff_uniqueness {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiSeparated f] [LocallyOfFiniteType f] [IsLocallyNoetherian Y] :
    Separated f ↔ ValuativeCriterion.Uniqueness f :=
  sorry

/-- A quasi-separated, locally finite-type morphism into a locally Noetherian algebraic
space is separated if and only if every DVR valuative square has at most one lift. -/
theorem iff_dvrUniqueness {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiSeparated f] [LocallyOfFiniteType f] [IsLocallyNoetherian Y] :
    Separated f ↔ ValuativeCriterion.DVR.Uniqueness f :=
  sorry

/-- A quasi-separated, locally finite-type morphism into a locally Noetherian algebraic
space is separated if and only if every DVR valuative square whose generic image has
codimension `0` has at most one lift. -/
theorem iff_dvrUniquenessAtCodimZero {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiSeparated f] [LocallyOfFiniteType f] [IsLocallyNoetherian Y] :
    Separated f ↔ ValuativeCriterion.DVR.UniquenessAtCodimZero f :=
  sorry

end Separated

end AlgebraicGeometry.AlgebraicSpace
