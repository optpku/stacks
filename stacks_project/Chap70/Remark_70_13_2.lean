/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap70.Lemma_70_13_3_AffineSpace

/-!
# Failure of embedding into affine space without local separatedness

Lemma 70.13.1 needs both quasi-separatedness and local separatedness of the
target. Dropping local separatedness already fails for quasi-separated targets;
whether local separatedness alone suffices is open.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The conclusion of Lemma 70.13.1: a morphism `f : U ⟶ X` of algebraic spaces
factors as an immersion into some relative affine space
`AffineSpace (ULift (Fin n)) X` over `X`. -/
def existsImmersionToAffineSpace {S : Scheme.{u}} {X U : AlgebraicSpace S}
    (f : U ⟶ X) : Prop :=
  ∃ (n : ℕ) (i : U ⟶ AffineSpace (ULift.{u} (Fin n)) X),
    IsImmersion i ∧ i ≫ AffineSpace.toBase (ULift.{u} (Fin n)) X = f

/-- A morphism of algebraic spaces admits an immersion into some relative affine
space over the target if and only if it equals the structure morphism of that
affine space after an immersion. -/
theorem existsImmersionToAffineSpace_iff {S : Scheme.{u}} {X U : AlgebraicSpace S}
    (f : U ⟶ X) :
    existsImmersionToAffineSpace f ↔
      ∃ (n : ℕ) (i : U ⟶ AffineSpace (ULift.{u} (Fin n)) X),
        IsImmersion i ∧ i ≫ AffineSpace.toBase (ULift.{u} (Fin n)) X = f :=
  sorry

/-- Remark 70.13.2 (1): Lemma 70.13.1 does not hold if the locally separated
hypothesis on `X` is dropped. There exist an affine algebraic space `U` and a
locally finite type morphism `f : U ⟶ X` into an absolutely quasi-separated
algebraic space `X` which does not immerse into any
`AffineSpace (ULift (Fin n)) X` over `X`. -/
@[stacks 088M]
theorem exists_quasiSeparated_without_immersion_to_affineSpace :
    ∃ (S : Scheme.{u}) (X U : AlgebraicSpace S) (f : U ⟶ X),
      IsAffine U ∧ LocallyOfFiniteType f ∧ IsAbsolutelyQuasiSeparated X ∧
        ¬ existsImmersionToAffineSpace f :=
  sorry

/-- Remark 70.13.2 (2): the open question whether Lemma 70.13.1 still holds if
only quasi-separatedness of `X` is dropped, keeping absolute local
separatedness. -/
@[stacks 088M]
def existsImmersionToAffineSpace_of_locallySeparated : Prop :=
  ∀ {S : Scheme.{u}} {X U : AlgebraicSpace S} (f : U ⟶ X),
    IsAffine U → LocallyOfFiniteType f → IsAbsolutelyLocallySeparated X →
      existsImmersionToAffineSpace f

/-- The locally-separated-only strengthening of Lemma 70.13.1 is the statement
that every locally finite type morphism from an affine algebraic space into an
absolutely locally separated algebraic space immerses into some relative affine
space over the target. -/
theorem existsImmersionToAffineSpace_of_locallySeparated_iff :
    existsImmersionToAffineSpace_of_locallySeparated ↔
      ∀ {S : Scheme.{u}} {X U : AlgebraicSpace S} (f : U ⟶ X),
        IsAffine U → LocallyOfFiniteType f → IsAbsolutelyLocallySeparated X →
          existsImmersionToAffineSpace f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
