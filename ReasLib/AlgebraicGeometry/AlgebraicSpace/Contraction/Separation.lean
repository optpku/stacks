module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.Functor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Separation

/-!
# Closed-immersion diagonals of contraction functors

Separatedness of the algebraic space and formal algebraic space in contraction
data implies that the diagonal of the compatible-triple functor on locally
Noetherian schemes is representable by closed immersions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite Limits TypeCat
open CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace.SchemeRealization
open AlgebraicGeometry.Scheme.Over

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ContractionSituation

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]

/-- The unique structure morphism from the formal algebraic space `W` to `S`. -/
def toBaseW (σ : ContractionSituation S) :
    σ.W ⟶ yoneda.obj (Over.mk (𝟙 S)) where
  app T := ofHom fun _ ↦ Over.homMk T.unop.hom
  naturality := sorry

/-- The component of the structure morphism of `W` sends every section over `T`
to the structure morphism `T.unop ⟶ Over.mk (𝟙 S)`. -/
theorem toBaseW_app (σ : ContractionSituation S) (T : (Over S)ᵒᵖ)
    (x : σ.W.obj T) :
    (toBaseW σ).app T x = Over.homMk T.unop.hom :=
  rfl

/-- Any morphism from `W` to `S` as a scheme over itself equals its canonical
structure morphism. -/
theorem eq_toBaseW {σ : ContractionSituation S}
    (f : σ.W ⟶ yoneda.obj (Over.mk (𝟙 S))) : f = toBaseW σ :=
  sorry

/-- If the algebraic space and formal algebraic space of contraction data are
separated over the base, the diagonal of the compatible-triple functor on
locally Noetherian schemes is representable by closed immersions. -/
theorem isClosedImmersion_diagonal (σ : ContractionSituation S)
    [Separated (toBase σ.X')] [FormalAlgebraicSpace.Separated (toBaseW σ)] :
    ((MorphismProperty.over
        (@AlgebraicGeometry.IsClosedImmersion : MorphismProperty Scheme.{u})).inverseImage
      (locallyNoetherian S).ι).relative uliftYoneda.{u + 1} (Limits.diag σ.functor) :=
  sorry

/-- If the algebraic space and formal algebraic space of contraction data are
separated over the base, the diagonal of the compatible-triple functor is
relatively representable with respect to `uliftYoneda`. -/
theorem relativelyRepresentable_diagonal (σ : ContractionSituation S)
    [Separated (toBase σ.X')] [FormalAlgebraicSpace.Separated (toBaseW σ)] :
    uliftYoneda.{u + 1}.relativelyRepresentable (Limits.diag σ.functor) :=
  (isClosedImmersion_diagonal σ).rep

end AlgebraicGeometry.AlgebraicSpace.ContractionSituation
