module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap76.Definition_76_23_2_FlatOnFiber

/-!
# Flatness of a morphism of algebraic spaces from fibrewise flatness over a Noetherian base

In a triangle `X ⟶ Y ⟶ Z` of algebraic spaces, if `X`, `Y`, `Z` are locally
Noetherian, `X` is flat over `Z`, and every fibre of `X` over a point of `|Z|`
is flat over the corresponding fibre of `Y`, then `X ⟶ Y` is flat. If that
morphism is also surjective, then `Y` is flat over `Z`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.24.2 (1): Let `S` be a scheme. Let `f : X ⟶ Y` and `h : Y ⟶ Z` be
morphisms of algebraic spaces over `S`. Assume `X`, `Y`, `Z` are locally
Noetherian, `X` is flat over `Z`, and for every `z : Points Z` the fibre of
`X` over `z` is flat over the fibre of `Y` over `z` in the sense of
`fiberFlatOver f h z`. Then `f` is flat. -/
@[stacks 0APS]
theorem Flat.of_fiberFlatOver_of_isLocallyNoetherian {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (h : Y ⟶ Z)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    [Flat (f ≫ h)] (h_fiber : ∀ z : Points Z, fiberFlatOver f h z) : Flat f :=
  sorry

/-- Lemma 76.24.2 (2): Let `S` be a scheme. Let `f : X ⟶ Y` and `h : Y ⟶ Z` be
morphisms of algebraic spaces over `S`. Assume `X`, `Y`, `Z` are locally
Noetherian, `X` is flat over `Z`, and for every `z : Points Z` one has
`fiberFlatOver f h z`. If `f` is also surjective, then `Y` is flat over `Z`. -/
@[stacks 0APS]
theorem Flat.base_of_fiberFlatOver_of_surjective_of_isLocallyNoetherian
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (h : Y ⟶ Z)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    [Flat (f ≫ h)] [Surjective f]
    (h_fiber : ∀ z : Points Z, fiberFlatOver f h z) : Flat h :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
