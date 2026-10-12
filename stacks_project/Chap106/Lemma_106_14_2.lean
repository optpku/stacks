/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap101.Definition_101_4_2_Separation
public import stacks_project.Chap101.Definition_101_8_1_Noetherian
public import stacks_project.Chap106.Theorem_106_13_9_Keel_Mori

/-!
# Quasi-separatedness and separatedness of Keel–Mori moduli spaces

If an algebraic stack has finite inertia and a uniform categorical moduli
space, then quasi-separatedness or separatedness of the stack passes to the
moduli algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids.Inertia
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 106.14.2 (1). Let `X` be an algebraic stack. Assume the inertia
morphism `forget X : I_X ⟶ X` is finite. Let `f : X ⟶ M.toGroupoids` be a
uniform categorical moduli space as constructed in Theorem 106.13.9. If `X`
is quasi-separated, then the algebraic space `M` is quasi-separated. -/
@[stacks 0DUY]
theorem isAbsolutelyQuasiSeparated_of_isUniformCategoricalModuliSpace
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [IsFinite (forget.{u + 1, u, u, u + 1} X)] {M : AlgebraicSpace S}
    (f : X ⟶ M.toGroupoids) [IsUniformCategoricalModuliSpace f]
    [IsQuasiSeparated X] : AlgebraicSpace.IsAbsolutelyQuasiSeparated M :=
  sorry

/-- Lemma 106.14.2 (2). Let `X` be an algebraic stack. Assume the inertia
morphism `forget X : I_X ⟶ X` is finite. Let `f : X ⟶ M.toGroupoids` be a
uniform categorical moduli space as constructed in Theorem 106.13.9. If `X`
is separated, then the algebraic space `M` is separated. -/
@[stacks 0DUY]
theorem isAbsolutelySeparated_of_isUniformCategoricalModuliSpace
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [IsFinite (forget.{u + 1, u, u, u + 1} X)] {M : AlgebraicSpace S}
    (f : X ⟶ M.toGroupoids) [IsUniformCategoricalModuliSpace f]
    [IsSeparated X] : AlgebraicSpace.IsAbsolutelySeparated M :=
  sorry

end AlgebraicGeometry.AlgebraicStack
