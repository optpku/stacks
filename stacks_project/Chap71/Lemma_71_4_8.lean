/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap67.Definition_67_33_1_ResidueFieldTrdeg
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_27_7_LocallyQuasiFinite
public import stacks_project.Chap71.Lemma_71_4_6_RelativeAssassin

/-!
# Lemma 71.4.8

Relative associated points of a quasi-coherent module on an algebraic space
are compatible with cartesian base change when the original morphism is
locally of finite type and the base change has residue-field transcendence
degree zero (in particular, when it is locally quasi-finite): the relative
assassin after pullback equals the preimage of the original relative assassin.
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

/-- Lemma 71.4.8: let `S` be a scheme and let `IsPullback g' f' f g` be a
cartesian square of algebraic spaces over `S`. Let `F` be a quasi-coherent
`𝒪_X`-module, and write `F'` for `(pullback g').obj F`. If `f` is locally of
finite type and the residue-field transcendence degree of `y' / g(y')` is `0`
for every point `y'` of `|Y'|` (in particular if `g` is locally quasi-finite),
then `relativeAssassin f' ((pullback g').obj F)` equals the preimage of
`relativeAssassin f F` under `Points.map g'`. -/
@[stacks 0CV3]
theorem eq_preimage_of_residueFieldTrdegEq_zero
    [AlgebraicSpace.LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] (sq : IsPullback g' f' f g)
    (hg : ∀ y' : Points Y', ResidueFieldTrdegEqAt g 0 y') :
    relativeAssassin f' ((pullback g').obj F) =
      Points.map g' ⁻¹' relativeAssassin f F :=
  sorry

/-- If `g` is locally quasi-finite, then under the same cartesian square,
locally-of-finite-type hypothesis, and quasi-coherent module `F`, the relative
assassin after pullback equals the preimage of the original relative assassin
under `Points.map g'`. -/
theorem eq_preimage_of_locallyQuasiFinite
    [AlgebraicSpace.LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] (sq : IsPullback g' f' f g)
    [AlgebraicSpace.LocallyQuasiFinite g] :
    relativeAssassin f' ((pullback g').obj F) =
      Points.map g' ⁻¹' relativeAssassin f F :=
  sorry

/-- A point of `X'` is relatively associated after cartesian base change if and
only if its image in `X` is relatively associated, when every point of `|Y'|`
has residue-field transcendence degree `0` over its image. -/
theorem mem_iff_map_mem_of_residueFieldTrdegEq_zero
    [AlgebraicSpace.LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] (sq : IsPullback g' f' f g)
    (hg : ∀ y' : Points Y', ResidueFieldTrdegEqAt g 0 y') {x' : Points X'} :
    x' ∈ relativeAssassin f' ((pullback g').obj F) ↔
      Points.map g' x' ∈ relativeAssassin f F :=
  sorry

end relativeAssassin

end AlgebraicGeometry.AlgebraicSpace.Modules
