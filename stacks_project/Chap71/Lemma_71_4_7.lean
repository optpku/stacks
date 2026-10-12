/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap71.Lemma_71_4_6_RelativeAssassin

/-!
# Lemma 71.4.7

Relative associated points of a quasi-coherent module on an algebraic space
are compatible with cartesian base change when the original morphism is
locally of finite type: the relative assassin after pullback is contained in
the preimage of the original relative assassin, and relatively associated
points lift through any compatible point of the base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
variable {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}

namespace relativeAssassin

/-- Lemma 71.4.7 (1): let `S` be a scheme and let `IsPullback g' f' f g` be a
cartesian square of algebraic spaces over `S`. Let `F` be a quasi-coherent
`𝒪_X`-module. If `f` is locally of finite type, then
`relativeAssassin f' ((pullback g').obj F)` is contained in the preimage of
`relativeAssassin f F` under `Points.map g'`. -/
@[stacks 0CV2]
theorem subset_preimage [AlgebraicSpace.LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] (sq : IsPullback g' f' f g) :
    relativeAssassin f' ((pullback g').obj F) ⊆
      Points.map g' ⁻¹' relativeAssassin f F :=
  sorry

/-- If a point of `X'` is relatively associated after cartesian base change,
then its image in `X` is relatively associated. -/
theorem mem_map_of_mem [AlgebraicSpace.LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] (sq : IsPullback g' f' f g)
    {x' : Points X'} (hx' : x' ∈ relativeAssassin f' ((pullback g').obj F)) :
    Points.map g' x' ∈ relativeAssassin f F :=
  sorry

/-- Lemma 71.4.7 (2): with the same cartesian square, locally-of-finite-type
hypothesis, and quasi-coherent module `F`, if `x` lies in
`relativeAssassin f F` and `y'` is a point of `Y'` with
`Points.map f x = Points.map g y'`, then there exists a point `x'` in
`relativeAssassin f' ((pullback g').obj F)` with `Points.map g' x' = x` and
`Points.map f' x' = y'`. -/
@[stacks 0CV2]
theorem exists_of_mem_map_eq [AlgebraicSpace.LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] (sq : IsPullback g' f' f g)
    {x : Points X} {y' : Points Y'} (hx : x ∈ relativeAssassin f F)
    (hxy : Points.map f x = Points.map g y') :
    ∃ x' : Points X',
      x' ∈ relativeAssassin f' ((pullback g').obj F) ∧
        Points.map g' x' = x ∧ Points.map f' x' = y' :=
  sorry

end relativeAssassin

end AlgebraicGeometry.AlgebraicSpace.Modules
