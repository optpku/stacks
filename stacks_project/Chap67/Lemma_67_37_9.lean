/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_37_9_SourceLocus

/-!
# Largest open subspace on which a morphism of algebraic spaces is smooth

There is a largest open subspace of the source on which a morphism of algebraic
spaces is smooth, and formation of this open commutes with cartesian base change
along morphisms that are flat and locally of finite presentation, and along
flat morphisms when the original morphism is locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.37.9 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. There is a largest open subspace `U ⊂ X` such that
the restriction of `f` along `U` is smooth. -/
@[stacks 0DZI]
theorem sourceLocus_isLargest {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    Smooth ((Smooth.sourceLocus f).ι ≫ f) ∧
      ∀ {U : AlgebraicSpace S} (i : U ⟶ X) [IsOpenImmersion i],
        Smooth (i ≫ f) →
          Set.range (Points.map i) ⊆
            Set.range (Points.map (Smooth.sourceLocus f).ι) :=
  sorry

namespace Smooth

/-- Lemma 67.37.9 (2): Formation of the largest open subspace on which `f` is
smooth commutes with cartesian base change along a morphism which is flat and
locally of finite presentation. -/
@[stacks 0DZI]
theorem sourceLocus_eq_openInverseImage_of_flat_locallyOfFinitePresentation
    {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hcart : IsPullback g' f' f g) [Flat g] [LocallyOfFinitePresentation g] :
    Set.range (Points.map (sourceLocus f').ι) =
      Set.range (Points.map (openInverseImageι g' (sourceLocus f).ι)) :=
  sorry

/-- Lemma 67.37.9 (3): Formation of the largest open subspace on which `f` is
smooth commutes with cartesian base change along a flat morphism, provided `f`
is locally of finite presentation. -/
@[stacks 0DZI]
theorem sourceLocus_eq_openInverseImage_of_flat_base
    {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hcart : IsPullback g' f' f g) [LocallyOfFinitePresentation f] [Flat g] :
    Set.range (Points.map (sourceLocus f').ι) =
      Set.range (Points.map (openInverseImageι g' (sourceLocus f).ι)) :=
  sorry

end Smooth

end AlgebraicGeometry.AlgebraicSpace
