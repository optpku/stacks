module

public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import stacks_project.Chap81.«81_11_0_1_Glueing»
public import stacks_project.Chap81.Situation_81_10_6_FormalGlueing
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap81.Lemma_81_3_4_SeparatedOver

/-!
# Full faithfulness of formal glueing on separated algebraic spaces

In the formal-glueing situation, the canonical functor `Over X ⥤ category f i`
from 81.11.0.1 is bijective on morphisms into an algebraic space separated over
`X`, and therefore full and faithful on `SeparatedMorphismOver X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.FormalGlueing

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FormalGlueing

/-- The canonical functor `Over X ⥤ category f i` is bijective on morphisms
into an algebraic space separated over `X`. -/
theorem functor_map_bijective {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] {X₁ X₂ : Over X} [Separated X₂.hom] :
    Function.Bijective
      ((functor f i).map :
        (X₁ ⟶ X₂) → ((functor f i).obj X₁ ⟶ (functor f i).obj X₂)) :=
  sorry

/-- The canonical functor `Over X ⥤ category f i` is injective on morphisms
into an algebraic space separated over `X`. -/
theorem functor_map_injective {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] {X₁ X₂ : Over X} [Separated X₂.hom] :
    Function.Injective
      ((functor f i).map :
        (X₁ ⟶ X₂) → ((functor f i).obj X₁ ⟶ (functor f i).obj X₂)) :=
  sorry

/-- The canonical functor `Over X ⥤ category f i` is surjective on morphisms
into an algebraic space separated over `X`. -/
theorem functor_map_surjective {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] {X₁ X₂ : Over X} [Separated X₂.hom] :
    Function.Surjective
      ((functor f i).map :
        (X₁ ⟶ X₂) → ((functor f i).obj X₁ ⟶ (functor f i).obj X₂)) :=
  sorry

/-- The Hom-level equivalence induced by the glueing functor when the target is
separated over `X`. -/
def functor_homEquiv {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] {X₁ X₂ : Over X} [Separated X₂.hom] :
    (X₁ ⟶ X₂) ≃ ((functor f i).obj X₁ ⟶ (functor f i).obj X₂) :=
  Equiv.ofBijective
    ((functor f i).map :
      (X₁ ⟶ X₂) → ((functor f i).obj X₁ ⟶ (functor f i).obj X₂))
    (functor_map_bijective f i)

/-- `functor_homEquiv f i` applies as `(functor f i).map`. -/
theorem functor_homEquiv_apply {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] {X₁ X₂ : Over X} [Separated X₂.hom] (φ : X₁ ⟶ X₂) :
    functor_homEquiv f i φ = (functor f i).map φ :=
  sorry

/-- The inverse of `functor_homEquiv f i` is the chosen preimage of a morphism
in `category f i`. -/
theorem functor_homEquiv_symm_apply {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] {X₁ X₂ : Over X} [Separated X₂.hom]
    (ψ : (functor f i).obj X₁ ⟶ (functor f i).obj X₂) :
    (functor f i).map ((functor_homEquiv f i).symm ψ) = ψ :=
  sorry

/-- The restriction of the glueing functor to algebraic spaces separated over
`X` is full. -/
instance separatedOver_functor_full {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] :
    (SeparatedMorphismOver.inclusion X ⋙ functor f i).Full :=
  sorry

/-- The restriction of the glueing functor to algebraic spaces separated over
`X` is faithful. -/
instance separatedOver_functor_faithful {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] :
    (SeparatedMorphismOver.inclusion X ⋙ functor f i).Faithful :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FormalGlueing

