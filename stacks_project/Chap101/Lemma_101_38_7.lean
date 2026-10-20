module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.SchemeTheoreticImage.PartialSection
import StacksCheckRecall

/-!
# Scheme-theoretic image of a partial section of algebraic stacks

A section of a separated morphism of algebraic stacks, representable by
algebraic spaces, over a quasi-compact open immersion has scheme-theoretic
image mapping isomorphically to the target over that open.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids.Hom (OpenImmersion)
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsSchemeTheoreticImage

/- Lemma 101.38.7: Let `f : X ⟶ Y` be a morphism of algebraic stacks which is
representable by algebraic spaces and separated. Let `ιV : V ⟶ Y` be a
quasi-compact open immersion, and let `s : V ⟶ X` be a section of `f` over
`V`. If `ι : Y' ⟶ X` is a scheme-theoretic image of `s`, then `Y' ⟶ Y` is an
isomorphism over `V`. -/
@[stacks 0CPW] #check
  (AlgebraicGeometry.AlgebraicStack.IsSchemeTheoreticImage.isEquivalence_snd_of_section :
    ∀ {S : Scheme.{u}} {X Y V Y' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack V] [AlgebraicStack Y']
      (f : X ⟶ Y) (hf : relativelyRepresentableByAlgebraicSpaces f) [Separated f]
      (ιV : V ⟶ Y) [OpenImmersion ιV] [QuasiCompact ιV]
      (s : V ⟶ X) (hs : s ≫ f ≅ ιV) (toImage : V ⟶ Y') (ι : Y' ⟶ X)
      [IsSchemeTheoreticImage s toImage ι],
      (CategoryTheory.FiberedCategoryOver.Groupoids.toBasedFunctor
        (CategoryTheory.TwoFibreProduct.snd.{u + 1, u, u + 1, u} (ι ≫ f) ιV)).IsEquivalence)

end AlgebraicGeometry.AlgebraicStack.IsSchemeTheoreticImage
