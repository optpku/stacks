module

public import stacks_project.Chap67.Lemma_67_31_3
public import stacks_project.Chap76.Theorem_76_22_1

/-!
# Base change of the relative flat locus on algebraic spaces

In a cartesian square of algebraic spaces whose base morphism is flat, the
relative-flatness locus of a finitely presented module is the preimage of the
open locus of Theorem 76.22.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 76.22.2: Let `S` be a scheme. Let `g' : X' ⟶ X`, `f' : X' ⟶ Y'`,
`f : X ⟶ Y`, `g : Y' ⟶ Y` form a cartesian diagram of algebraic spaces over
`S`. Let `F` be a quasi-coherent `𝒪_X`-module. Assume `g` is flat, `f` is
locally of finite presentation, and `F` is locally of finite presentation.
Then `flatOverLocus ((pullback g').obj F) f'` is the inverse image of
`flatOverLocus F f` under the continuous map `Points.map g'`. -/
@[stacks 05WW]
theorem flatOverLocus_eq_preimage {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hcart : IsPullback g' f' f g) [Flat g] [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsFinitePresentation] :
    flatOverLocus ((pullback g').obj F) f' = Points.map g' ⁻¹' flatOverLocus F f :=
  sorry

/-- A point of `|X'|` lies in the relative-flatness locus of `(pullback g').obj F`
over `Y'` if and only if its image under `Points.map g'` lies in
`flatOverLocus F f`. -/
theorem mem_flatOverLocus_eq_preimage {S : Scheme.{u}}
    {X' X Y' Y : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g) [Flat g]
    [LocallyOfFinitePresentation f] (F : X.Modules) [F.IsFinitePresentation]
    (x' : Points X') :
    x' ∈ flatOverLocus ((pullback g').obj F) f' ↔
      Points.map g' x' ∈ flatOverLocus F f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
