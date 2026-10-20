module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient.StructureMap
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Universal injectivity and the absolute Galois quotient

The absolute Galois quotient of the spectrum of the complex algebraic numbers
has a universally injective structure morphism to the rational spectrum. Its
nonempty reduced identity fibre is not a purely inseparable field spectrum.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient

/-- The structure morphism of the absolute Galois quotient is universally injective:
its relative diagonal is representably surjective. -/
theorem universallyInjective_toSpec :
    (MorphismProperty.over (@Surjective)).relative uliftYoneda.{1}
      (pullback.diagonal toSpec).hom := sorry

/-- The absolute Galois quotient has a universally injective structure morphism and a
reduced étale atlas, but its nonempty identity fibre has no presentation over the rational
spectrum as the spectrum of a purely inseparable rational field extension. -/
theorem not_radicial_toSpec :
    (MorphismProperty.over (@Surjective)).relative uliftYoneda.{1}
        (pullback.diagonal toSpec).hom ∧
      ((MorphismProperty.over (@Etale)).relative uliftYoneda.{1} atlas.hom ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over base) atlas.hom ∧
        AlgebraicGeometry.IsReduced cover.left) ∧
      Nonempty (sheafOfPoints.obj.obj (op cover)) ∧
      ∀ (L : Type) [Field L] [Algebra ℚ L] [IsPurelyInseparable ℚ L]
        (e : sheafOfPoints ≅
          (Scheme.fppfTopology.over base).uliftYoneda.{1}.obj
            (Over.mk (FieldExtension.specMap ℚ L))),
        e.hom ≫ (Scheme.fppfTopology.over base).uliftYoneda.{1}.map (specToBase L) ≠
          toSpec := by
  refine ⟨universallyInjective_toSpec, ?_⟩
  sorry

end AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient
