/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Ideal

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

/-- For an open subspace of a quasi-compact quasi-separated algebraic space,
quasi-compactness of the inclusion, quasi-compactness of the open subspace,
and existence of a finite type quasi-coherent ideal sheaf cutting out its
closed complement are equivalent. -/
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
  Iff.rfl

/-- The inclusion of an open subspace of a quasi-compact quasi-separated
algebraic space is quasi-compact if and only if the open subspace is
quasi-compact. -/
theorem quasiCompact_iff_isQuasiCompact [IsQuasiCompact X]
    [IsAbsolutelyQuasiSeparated X] (U : OpenSubspace X) :
    QuasiCompact U.ι ↔ IsQuasiCompact U.X :=
  (quasiCompact_tfae U).out 0 1

/-- The inclusion of an open subspace of a quasi-compact quasi-separated
algebraic space is quasi-compact if and only if the closed complement is cut
out by a finite type quasi-coherent ideal sheaf. -/
theorem quasiCompact_iff_existsFiniteTypeVanishingIdeal [IsQuasiCompact X]
    [IsAbsolutelyQuasiSeparated X] (U : OpenSubspace X) :
    QuasiCompact U.ι ↔ existsFiniteTypeVanishingIdeal U :=
  (quasiCompact_tfae U).out 0 2

/-- An open subspace of a quasi-compact quasi-separated algebraic space is
quasi-compact if and only if the closed complement is cut out by a finite type
quasi-coherent ideal sheaf. -/
theorem isQuasiCompact_iff_existsFiniteTypeVanishingIdeal [IsQuasiCompact X]
    [IsAbsolutelyQuasiSeparated X] (U : OpenSubspace X) :
    IsQuasiCompact U.X ↔ existsFiniteTypeVanishingIdeal U :=
  (quasiCompact_tfae U).out 1 2

end AlgebraicGeometry.AlgebraicSpace.OpenSubspace
