module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import stacks_project.Chap42.Lemma_42_62_3_Gysin
public import stacks_project.Chap42.Lemma_42_62_3_IntersectionProduct

/-!
# Projection formula for the intersection product

This file records that a proper morphism of schemes smooth over a field has a Gysin
map, and that pushforward of the Section 42.62 intersection product satisfies the
projection formula against Gysin pullback.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.BivariantClass AlgebraicGeometry.ChowGroup
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules hiding dual

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

variable {k : Type u} [Field k]

/-- Lemma 42.62.4 (1): for a field `k` and a proper morphism `f : X ⟶ Y` of schemes
smooth over `k`, the Gysin map exists for `f`. -/
@[stacks 0FFC]
theorem hasGysinMap_of_proper_smooth {X Y : SchemeOverField k}
    [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y) [IsProper f.left] :
    HasGysinMap f := sorry

end AlgebraicGeometry.BivariantClass

namespace AlgebraicGeometry.ChowGroup.Total

variable {k : Type u} [Field k]

/-- Lemma 42.62.4 (2): for a field `k` and a proper morphism `f : X ⟶ Y` of schemes
smooth over `k`, the projection formula
`Total.map f (intersectionProduct α (gysinMap β)) =
intersectionProduct (Total.map f α) β` holds in `CH_*(Y)`. -/
@[stacks 0FFC]
theorem intersectionProduct_projection_formula {X Y : SchemeOverField k}
    [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y) [IsProper f.left]
    [IsRegularImmersion (graph f).left]
    (e : Scheme.Modules.dual (normalSheaf (graph f).left) ≅
      conormalSheaf (graph f).left)
    (D : GraphSpecialization f e) (r t rX rY : ℕ)
    [Scheme.Hom.RelativeDimension (prod.snd : X ⨯ Y ⟶ Y).left t]
    [IsFiniteLocallyFreeOfRank rX (conormalSheaf (diagonal X).left)]
    [IsFiniteLocallyFreeOfRank rY (conormalSheaf (diagonal Y).left)]
    (DX : DiagonalSpecialization X rX) (DY : DiagonalSpecialization Y rY)
    (alpha : Total (fun _ ↦ 0) X) (beta : Total (fun _ ↦ 0) Y) :
    map (fun _ ↦ 0) f
        (intersectionProduct X rX DX alpha (gysinMap f e D r t beta)) =
      intersectionProduct Y rY DY (map (fun _ ↦ 0) f alpha) beta := sorry

end AlgebraicGeometry.ChowGroup.Total
