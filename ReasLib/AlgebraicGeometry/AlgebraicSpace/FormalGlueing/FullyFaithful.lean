module

public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormalGlueing.Spaces
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormalGlueing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SeparatedOver

/-!
# Full faithfulness of formal glueing on separated algebraic spaces

In the formal-glueing situation, the canonical functor `Over X ⥤ category f i`
is bijective on morphisms into an algebraic space separated over `X`, and therefore full and faithful on `SeparatedMorphismOver X`.
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

