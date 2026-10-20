module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap71.Lemma_71_4_6_RelativeAssassin

/-!
# Lemma 77.6.2

Relative associated points of a quasi-coherent module on an algebraic space
that are covered by a morphism remain covered after arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

namespace relativeAssassin

/-- Lemma 77.6.2: Let `Y` be an algebraic space over a scheme `S`. Let
`g : X' ⟶ X` be a morphism of algebraic spaces over `Y` with `X` locally of
finite type over `Y`. Let `F` be a quasi-coherent `𝒪_X`-module. If
`Ass_{X/Y}(F) ⊆ g(|X'|)`, then for any morphism `Z ⟶ Y` one has
`Ass_{X_Z/Z}(F_Z) ⊆ g_Z(|X'_Z|)`.
Here `Ass_{X/Y}(F)` is `relativeAssassin f F` with structure map `f : X ⟶ Y`,
`g(|X'|)` is `Set.range (Points.map g)`, `X_Z` is `Limits.pullback f h`,
`F_Z` is `(pullback (Limits.pullback.fst f h)).obj F`, `X'_Z` is identified
with `X_Z ×_X X'`, and `g_Z` is
`Limits.pullback.fst (Limits.pullback.fst f h) g`. -/
@[stacks 0CW2]
theorem subset_range_afterBaseChange {S : Scheme.{u}} {Y X X' : AlgebraicSpace S}
    (f : X ⟶ Y) (g : X' ⟶ X) [LocallyOfFiniteType f] (F : X.Modules)
    [F.IsQuasicoherent] (hAss : relativeAssassin f F ⊆ Set.range (Points.map g))
    {Z : AlgebraicSpace S} (h : Z ⟶ Y) :
    relativeAssassin (Limits.pullback.snd f h) ((pullback (Limits.pullback.fst f h)).obj F) ⊆
      Set.range (Points.map (Limits.pullback.fst (Limits.pullback.fst f h) g)) :=
  sorry

/-- If a point of `|X_Z|` is relatively associated after base change along
`h : Z ⟶ Y`, then it lies in the image of `|g_Z|`. -/
theorem mem_range_afterBaseChange {S : Scheme.{u}} {Y X X' : AlgebraicSpace S}
    (f : X ⟶ Y) (g : X' ⟶ X) [LocallyOfFiniteType f] (F : X.Modules)
    [F.IsQuasicoherent] (hAss : relativeAssassin f F ⊆ Set.range (Points.map g))
    {Z : AlgebraicSpace S} (h : Z ⟶ Y) {x : Points (Limits.pullback f h)}
    (hx : x ∈ relativeAssassin (Limits.pullback.snd f h)
      ((pullback (Limits.pullback.fst f h)).obj F)) :
    x ∈ Set.range (Points.map (Limits.pullback.fst (Limits.pullback.fst f h) g)) :=
  sorry

end relativeAssassin

end AlgebraicGeometry.AlgebraicSpace.Modules
