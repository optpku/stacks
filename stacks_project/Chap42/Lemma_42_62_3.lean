/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import stacks_project.Chap42.Lemma_42_62_3_Gysin
public import stacks_project.Chap42.Lemma_42_62_3_IntersectionProduct

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.BivariantClass AlgebraicGeometry.ChowGroup
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules hiding dual

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/-- Lemma 42.62.3 (1): Let `k` be a field. Let `f : X ⟶ Y` be a morphism of schemes
smooth over `k`. Then the Gysin map exists for `f`. -/
@[stacks 0FFB]
theorem hasGysinMap_of_smooth {k : Type u} [Field k] {X Y : SchemeOverField k}
    [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y) : HasGysinMap f := sorry

end AlgebraicGeometry.BivariantClass

namespace AlgebraicGeometry.ChowGroup

/-- Lemma 42.62.3 (2): Let `k` be a field. Let `f : X ⟶ Y` be a morphism of schemes
smooth over `k`. Then `f!(α · β) = f!α · f!β` on total Chow homology, where `·` is
the Section 42.62 intersection product. -/
@[stacks 0FFB]
theorem gysin_intersectionProduct {k : Type u} [Field k] {X Y : SchemeOverField k}
    [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y)
    [IsRegularImmersion (graph f).left]
    (e : Scheme.Modules.dual (normalSheaf (graph f).left) ≅
      conormalSheaf (graph f).left)
    (D : GraphSpecialization f e) (r t rX rY : ℕ)
    [Scheme.Hom.RelativeDimension (prod.snd : X ⨯ Y ⟶ Y).left t]
    [IsFiniteLocallyFreeOfRank rX (conormalSheaf (diagonal X).left)]
    [IsFiniteLocallyFreeOfRank rY (conormalSheaf (diagonal Y).left)]
    (DX : DiagonalSpecialization X rX) (DY : DiagonalSpecialization Y rY)
    (alpha beta : Total (fun _ ↦ 0) Y) :
    gysinMap f e D r t (Total.intersectionProduct Y rY DY alpha beta) =
      Total.intersectionProduct X rX DX (gysinMap f e D r t alpha)
        (gysinMap f e D r t beta) := sorry

end AlgebraicGeometry.ChowGroup
