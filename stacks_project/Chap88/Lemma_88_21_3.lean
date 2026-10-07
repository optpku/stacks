module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_24_3
public import stacks_project.Chap88.Definition_88_21_1

/-!
# Composition of rig-surjective morphisms

The composition of locally of finite type rig-surjective morphisms of locally
Noetherian formal algebraic spaces is again rig-surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FormalAlgebraicSpace

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.RigSurjective

/-- Lemma 88.21.3: Let `S` be a scheme. Let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of formal algebraic spaces over `S`. Assume `X`, `Y`, `Z` are locally
Noetherian and `f` and `g` locally of finite type. Then if `f` and `g` are
rig-surjective, so is `g ∘ f`. In Lean composition this is
`RigSurjective f → RigSurjective g → RigSurjective (f ≫ g)`. -/
@[stacks 0AQR]
instance comp {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    [RigSurjective f] [RigSurjective g] : RigSurjective (f ≫ g) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace.RigSurjective
