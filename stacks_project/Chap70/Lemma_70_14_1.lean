/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap66.Lemma_66_12_3
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Definition_67_14_4_IdealSubobject
public import stacks_project.Chap67.Lemma_67_13_1_Correspondence

/-!
# Quasi-compact open subspaces of quasi-compact quasi-separated algebraic spaces

On a quasi-compact quasi-separated algebraic space, an open subspace is
quasi-compact if and only if its inclusion is a quasi-compact morphism, if and
only if the closed complement is the vanishing locus of a finite type
quasi-coherent ideal sheaf.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.OpenSubspace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- An open subspace is cut out as the complement of the vanishing locus of a
finite type quasi-coherent ideal sheaf of `𝒪_X`. -/
def existsFiniteTypeVanishingIdeal (U : OpenSubspace X) : Prop :=
  ∃ (I : IdealSubobject X) (_ : IsQuasiCoherent I),
    (I : X.Modules).IsFiniteType ∧
      (ClosedSubspace.ofQuasiCoherentIdeal I).pointsSet = U.pointsSetᶜ

/-- Lemma 70.14.1: let `S` be a scheme. Let `X` be a quasi-compact and
quasi-separated algebraic space. Let `U` be an open subspace of `X`. The
following are equivalent: `QuasiCompact U.ι`, `IsQuasiCompact U.X`, and
`existsFiniteTypeVanishingIdeal U`. -/
@[stacks 0855]
theorem quasiCompact_tfae [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (U : OpenSubspace X) :
    List.TFAE [QuasiCompact U.ι, IsQuasiCompact U.X,
      existsFiniteTypeVanishingIdeal U] :=
  sorry

/-- The finite type vanishing-ideal condition unfolds as existence of a
quasi-coherent finite type ideal subobject whose vanishing locus is the
complement of `U.pointsSet`. -/
theorem existsFiniteTypeVanishingIdeal_iff (U : OpenSubspace X) :
    existsFiniteTypeVanishingIdeal U ↔
      ∃ (I : IdealSubobject X) (_ : IsQuasiCoherent I),
        (I : X.Modules).IsFiniteType ∧
          (ClosedSubspace.ofQuasiCoherentIdeal I).pointsSet = U.pointsSetᶜ :=
  sorry

/-- The inclusion of an open subspace of a quasi-compact quasi-separated
algebraic space is quasi-compact if and only if the open subspace is
quasi-compact. -/
theorem quasiCompact_iff_isQuasiCompact [IsQuasiCompact X]
    [IsAbsolutelyQuasiSeparated X] (U : OpenSubspace X) :
    QuasiCompact U.ι ↔ IsQuasiCompact U.X :=
  sorry

/-- The inclusion of an open subspace of a quasi-compact quasi-separated
algebraic space is quasi-compact if and only if the closed complement is cut
out by a finite type quasi-coherent ideal sheaf. -/
theorem quasiCompact_iff_existsFiniteTypeVanishingIdeal [IsQuasiCompact X]
    [IsAbsolutelyQuasiSeparated X] (U : OpenSubspace X) :
    QuasiCompact U.ι ↔ existsFiniteTypeVanishingIdeal U :=
  sorry

/-- An open subspace of a quasi-compact quasi-separated algebraic space is
quasi-compact if and only if the closed complement is cut out by a finite type
quasi-coherent ideal sheaf. -/
theorem isQuasiCompact_iff_existsFiniteTypeVanishingIdeal [IsQuasiCompact X]
    [IsAbsolutelyQuasiSeparated X] (U : OpenSubspace X) :
    IsQuasiCompact U.X ↔ existsFiniteTypeVanishingIdeal U :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.OpenSubspace
