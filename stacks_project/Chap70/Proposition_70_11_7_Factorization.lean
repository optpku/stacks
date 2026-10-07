module

public import Mathlib.CategoryTheory.MorphismProperty.Factorization
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation

/-!
# Closed-immersion factorizations of finite type separated morphisms

A finite type separated morphism of algebraic spaces, with quasi-compact
quasi-separated target, factors as a closed immersion followed by a
separated morphism of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A finite type separated morphism of algebraic spaces over a scheme, with
quasi-compact quasi-separated target, factors as a closed immersion followed by
a separated morphism of finite presentation. -/
theorem exists_closedImmersion_factorization_of_finiteType_separated
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [FiniteType f] [Separated f]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y] :
    (MorphismProperty.comp
      (@IsClosedImmersion S : MorphismProperty (AlgebraicSpace S))
      ((@FinitePresentation S : MorphismProperty (AlgebraicSpace S)) ⊓
        (@Separated S : MorphismProperty (AlgebraicSpace S)))) f :=
  sorry

/-- Such a morphism factors as a closed immersion over the target followed by a
separated morphism of finite presentation if and only if there is an intermediate
algebraic space realizing that factorization. -/
theorem exists_closedImmersion_factorization_of_finiteType_separated_iff
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [FiniteType f] [Separated f]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y] :
    (MorphismProperty.comp
      (@IsClosedImmersion S : MorphismProperty (AlgebraicSpace S))
      ((@FinitePresentation S : MorphismProperty (AlgebraicSpace S)) ⊓
        (@Separated S : MorphismProperty (AlgebraicSpace S)))) f ↔
      ∃ (X' : AlgebraicSpace S) (i : X ⟶ X') (f' : X' ⟶ Y),
        IsClosedImmersion i ∧ FinitePresentation f' ∧ Separated f' ∧ i ≫ f' = f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
