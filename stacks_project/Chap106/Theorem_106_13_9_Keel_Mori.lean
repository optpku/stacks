/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_4_1_Separation
public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact
public import stacks_project.Chap101.Definition_101_10_1_Integral
public import stacks_project.Chap101.Definition_101_15_2_UniversalHomeomorphism
public import stacks_project.Chap101.Lemma_101_5_1
public import stacks_project.Chap106.Definition_106_12_1_Moduli

/-!
# The Keel–Mori theorem

If the inertia morphism of an algebraic stack is finite, then the stack
admits a uniform categorical moduli space. That morphism is separated,
quasi-compact, and a universal homeomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids.Inertia
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Theorem 106.13.9 (Keel-Mori) (1). Let `X` be an algebraic stack. Assume
the inertia morphism `forget X : I_X ⟶ X` is finite. Then there exists a
uniform categorical moduli space `f : X ⟶ M.toGroupoids`. -/
@[stacks 0DUT]
theorem exists_isUniformCategoricalModuliSpace_of_isFinite_inertia
    {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsFinite (forget.{u + 1, u, u, u + 1} X)] :
    ∃ (M : AlgebraicSpace S) (f : X ⟶ M.toGroupoids),
      IsUniformCategoricalModuliSpace f :=
  sorry

/-- Theorem 106.13.9 (Keel-Mori) (2). Let `X` be an algebraic stack. Assume
the inertia morphism `forget X : I_X ⟶ X` is finite. A uniform categorical
moduli space `f : X ⟶ M.toGroupoids` is separated. -/
@[stacks 0DUT, instance]
instance instSeparated_of_isFinite_inertia {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X]
    [IsFinite (forget.{u + 1, u, u, u + 1} X)] {M : AlgebraicSpace S}
    (f : X ⟶ M.toGroupoids) [IsUniformCategoricalModuliSpace f] :
    Separated f :=
  sorry

/-- Theorem 106.13.9 (Keel-Mori) (3). Let `X` be an algebraic stack. Assume
the inertia morphism `forget X : I_X ⟶ X` is finite. A uniform categorical
moduli space `f : X ⟶ M.toGroupoids` is quasi-compact. -/
@[stacks 0DUT, instance]
instance instQuasiCompact_of_isFinite_inertia {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X]
    [IsFinite (forget.{u + 1, u, u, u + 1} X)] {M : AlgebraicSpace S}
    (f : X ⟶ M.toGroupoids) [IsUniformCategoricalModuliSpace f] :
    QuasiCompact f :=
  sorry

/-- Theorem 106.13.9 (Keel-Mori) (4). Let `X` be an algebraic stack. Assume
the inertia morphism `forget X : I_X ⟶ X` is finite. A uniform categorical
moduli space `f : X ⟶ M.toGroupoids` is a universal homeomorphism. -/
@[stacks 0DUT, instance]
instance instUniversalHomeomorphism_of_isFinite_inertia {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X]
    [IsFinite (forget.{u + 1, u, u, u + 1} X)] {M : AlgebraicSpace S}
    (f : X ⟶ M.toGroupoids) [IsUniformCategoricalModuliSpace f] :
    UniversalHomeomorphism f :=
  sorry

end AlgebraicGeometry.AlgebraicStack
