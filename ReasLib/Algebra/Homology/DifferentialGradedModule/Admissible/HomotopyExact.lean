/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Admissible
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Homotopy.Property

/-!
# Homotopy Exactness of Admissible DG-Module Rows

The reusable core only uses a chosen graded splitting of the middle row.  Admissibility supplies
that splitting choice-free, while the Stacks-facing theorem restores the three-row diagram and
all four endpoint-zero homotopy-commutativity assumptions.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory

namespace DifferentialGradedModule
namespace ShortComplex

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}

/-- A graded splitting makes the middle row exact in the DG homotopy category: a composite
through its middle object vanishes when the two neighboring composites vanish. -/
@[stacks 09JY "homotopy exactness from a graded splitting"]
theorem comp_eq_zero_inK
    {S : ShortComplex (DifferentialGradedModule.{u, w} A)} (sigma : GradedSplitting S)
    {X Y : DifferentialGradedModule.{u, w} A}
    {b : X ⟶ S.X₂} {b' : S.X₂ ⟶ Y}
    (hb : (toK A).map b ≫ (toK A).map S.g = 0)
    (hb' : (toK A).map S.f ≫ (toK A).map b' = 0) :
    (toK A).map b ≫ (toK A).map b' = 0 := sorry

/-- An admissibly short-exact middle row satisfies the same exactness criterion in the DG
homotopy category. -/
theorem comp_eq_zero_inK_of_admissible
    {S : ShortComplex (DifferentialGradedModule.{u, w} A)}
    (hS : IsAdmissibleShortExact S)
    {X Y : DifferentialGradedModule.{u, w} A}
    {b : X ⟶ S.X₂} {b' : S.X₂ ⟶ Y}
    (hb : (toK A).map b ≫ (toK A).map S.g = 0)
    (hb' : (toK A).map S.f ≫ (toK A).map b' = 0) :
    (toK A).map b ≫ (toK A).map b' = 0 := sorry

/-- Concrete null-homotopies of the two neighboring composites yield a null-homotopy of the
composite through an admissibly short-exact middle row. -/
theorem comp_nullHomotopic_of_admissible
    {S : ShortComplex (DifferentialGradedModule.{u, w} A)}
    (hS : IsAdmissibleShortExact S)
    {X Y : DifferentialGradedModule.{u, w} A}
    {b : X ⟶ S.X₂} {b' : S.X₂ ⟶ Y}
    (hb : Nonempty (Homotopy (b ≫ S.g) 0))
    (hb' : Nonempty (Homotopy (S.f ≫ b') 0)) :
    Nonempty (Homotopy (b ≫ b') 0) := sorry

/-- Lemma 22.7.6 (09JY): for three admissible short exact rows and consecutive middle maps,
homotopy commutativity of the two zero-endpoint diagrams makes the middle composite
null-homotopic. -/
@[stacks 09JY]
theorem comp_nullHomotopic_of_rows
    {S₁ S₂ S₃ : ShortComplex (DifferentialGradedModule.{u, w} A)}
    (hS₁ : IsAdmissibleShortExact S₁) (hS₂ : IsAdmissibleShortExact S₂)
    (hS₃ : IsAdmissibleShortExact S₃)
    {b : S₁.X₂ ⟶ S₂.X₂} {b' : S₂.X₂ ⟶ S₃.X₂}
    (hf : Nonempty (Homotopy (S₁.f ≫ b) 0))
    (hg : Nonempty (Homotopy (b ≫ S₂.g) 0))
    (hf' : Nonempty (Homotopy (S₂.f ≫ b') 0))
    (hg' : Nonempty (Homotopy (b' ≫ S₃.g) 0)) :
    Nonempty (Homotopy (b ≫ b') 0) := sorry

end ShortComplex
end DifferentialGradedModule
