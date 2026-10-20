module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Square
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening
public import Mathlib.CategoryTheory.EssentialImage

/-!
# Pseudo-coherent derived modules on pushouts of algebraic spaces

Pseudo-coherent derived modules with an identification on the overlap glue
across a pushout of a thickening along an affine morphism.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open scoped CategoricalPullback

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- For a pushout of a thickening along an affine morphism, every pair of
pseudo-coherent derived modules with an isomorphism of their derived pullbacks
to the overlap lies in the essential image of the derived-pullback comparison. -/
theorem modulePullbackDerived.pushoutSquareFunctor_essImage_of_pseudoCoherent
    {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {i : X ⟶ X'} {f : X ⟶ Y} {f' : X' ⟶ Y'} {j : Y ⟶ Y'}
    [IsThickening i] [Affine f]
    (h : IsPushout i f f' j) (M : ModuleDerived Y) (K' : ModuleDerived X')
    (hM : IsPseudoCoherent Y M) (hK' : IsPseudoCoherent X' K')
    (α : (modulePullbackDerived f).obj M ≅ (modulePullbackDerived i).obj K') :
    (modulePullbackDerived.pushoutSquareFunctor h.toCommSq).essImage
      (CategoricalPullback.mk M K' α) := sorry

/-- An object of the categorical pullback with pseudo-coherent components lies
in the essential image of derived pullback from a pushout of a thickening along
an affine morphism. -/
theorem modulePullbackDerived.pushoutSquareFunctor_essImage_of_pseudoCoherent_obj
    {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {i : X ⟶ X'} {f : X ⟶ Y} {f' : X' ⟶ Y'} {j : Y ⟶ Y'}
    [IsThickening i] [Affine f]
    (h : IsPushout i f f' j) (T : (modulePullbackDerived f) ⊡ (modulePullbackDerived i))
    (hM : IsPseudoCoherent Y T.fst) (hK' : IsPseudoCoherent X' T.snd) :
    (modulePullbackDerived.pushoutSquareFunctor h.toCommSq).essImage T := sorry

end AlgebraicGeometry.AlgebraicSpace
