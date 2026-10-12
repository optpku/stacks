/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_24_3
public import stacks_project.Chap88.Definition_88_21_1

/-!
# Left cancellation of rig-surjectivity along a monomorphism

If a composite of locally finite type morphisms of locally Noetherian formal
algebraic spaces is rig-surjective and the second factor is a monomorphism,
then the first factor is rig-surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FormalAlgebraicSpace

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

namespace RigSurjective

/-- Lemma 88.21.5: Let `S` be a scheme. Let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms locally of finite type of locally Noetherian formal algebraic spaces
over `S`. If `g ∘ f` is rig-surjective and `g` is a monomorphism, then `f` is
rig-surjective. In Lean composition this is the implication
`RigSurjective (f ≫ g) → Mono g → RigSurjective f`. -/
@[stacks 0GH5]
theorem of_comp_mono {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] [RigSurjective (f ≫ g)] [Mono g] :
    RigSurjective f :=
  sorry

end RigSurjective

end AlgebraicGeometry.FormalAlgebraicSpace
