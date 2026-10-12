/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Factorization
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation

/-!
# Closed-immersion factorizations of locally of finite type morphisms

A locally of finite type morphism of algebraic spaces, with quasi-compact
quasi-separated source and target, factors as a closed immersion followed by
a morphism of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A locally of finite type morphism of algebraic spaces over a scheme, with
quasi-compact quasi-separated source and target, factors as a closed immersion
followed by a morphism of finite presentation. -/
theorem exists_closedImmersion_factorization_of_locallyOfFiniteType
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y] :
    (MorphismProperty.comp
      (@IsClosedImmersion S : MorphismProperty (AlgebraicSpace S))
      (@FinitePresentation S : MorphismProperty (AlgebraicSpace S))) f :=
  sorry

/-- Such a morphism factors as a closed immersion over the target followed by a
morphism of finite presentation if and only if there is an intermediate algebraic
space realizing that factorization. -/
theorem exists_closedImmersion_factorization_of_locallyOfFiniteType_iff
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y] :
    (MorphismProperty.comp
      (@IsClosedImmersion S : MorphismProperty (AlgebraicSpace S))
      (@FinitePresentation S : MorphismProperty (AlgebraicSpace S))) f ↔
      ∃ (X' : AlgebraicSpace S) (i : X ⟶ X') (f' : X' ⟶ Y),
        IsClosedImmersion i ∧ FinitePresentation f' ∧ i ≫ f' = f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
