module

public import ReasLib.AlgebraicGeometry.Scheme.Flattening.InDimensions.Etale
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme.Flattening

/- Lemma 38.27.2 (1): the flat-in-dimensions subfunctor for a module is contained in
the corresponding subfunctor after pulling the module back along an étale morphism. -/
@[stacks 05UD] #check
  (AlgebraicGeometry.Scheme.Flattening.flatInDimensionsSubfunctor.le_of_etale :
    ∀ {X X' S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (n : ℕ)
      (h : X' ⟶ X) [Etale h],
      flatInDimensionsSubfunctor f ℱ n ≤
        flatInDimensionsSubfunctor (h ≫ f) ((Scheme.Modules.pullback h).obj ℱ) n)

/- Lemma 38.27.2 (2): if the image of an étale morphism contains the relative assassin,
then pulling back the module along it does not change the flat-in-dimensions subfunctor. -/
@[stacks 05UD] #check
  (AlgebraicGeometry.Scheme.Flattening.flatInDimensionsSubfunctor.eq_of_relativeAssassin_subset_range :
    ∀ {X X' S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (n : ℕ)
      (h : X' ⟶ X) [Etale h]
      (_ : Scheme.Modules.relativeAssassin f ℱ ⊆ Set.range h.base),
      flatInDimensionsSubfunctor f ℱ n =
        flatInDimensionsSubfunctor (h ≫ f) ((Scheme.Modules.pullback h).obj ℱ) n)

end Scheme.Flattening
end AlgebraicGeometry
