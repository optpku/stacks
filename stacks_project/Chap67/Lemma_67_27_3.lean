module

public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_27_3_QuasiFinite
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Composition of quasi-finite morphisms of algebraic spaces

The composition of a pair of quasi-finite morphisms of algebraic spaces is
quasi-finite, and the same holds for morphisms that are locally quasi-finite
in the Stacks sense (locally of finite type and locally quasi-finite).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.27.3 (1): The composition of quasi-finite morphisms of algebraic
spaces is quasi-finite. -/
@[stacks 03XK]
instance quasiFinite_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@QuasiFinite S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of quasi-finite morphisms of algebraic spaces is
quasi-finite. -/
instance quasiFinite_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiFinite f] [QuasiFinite g] :
    QuasiFinite (f ≫ g) := sorry

/-- Lemma 67.27.3 (2): The composition of locally quasi-finite morphisms of
algebraic spaces is locally quasi-finite. -/
@[stacks 03XK]
instance locallyQuasiFinite_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@LocallyOfFiniteType S ⊓ @LocallyQuasiFinite S :
        MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of locally quasi-finite morphisms of algebraic spaces is
locally quasi-finite. -/
theorem locallyQuasiFinite_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [LocallyOfFiniteType g] [LocallyQuasiFinite g] :
    LocallyOfFiniteType (f ≫ g) ∧ LocallyQuasiFinite (f ≫ g) := sorry

end AlgebraicGeometry.AlgebraicSpace
