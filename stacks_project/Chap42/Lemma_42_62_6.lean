/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap42.Lemma_42_62_2_Comparison
public import stacks_project.Chap42.Lemma_42_59_8

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle
open AlgebraicGeometry.Scheme.Modules hiding dual
open AlgebraicGeometry.BivariantClass (overHom_eq_over castRelativeDegree totalCap)

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

variable {k : Type u} [Field k]

/-- The grading identity comparing the intersection product of a class of degree `n` with a
class of dimension `e` against a diagonal of rank `r` to the Gysin shift of rank `c` when
`r = c + e`. -/
theorem intersectionProduct_gysin_degree (n : ℤ) (r e c : ℕ) (h : r = c + e) :
    n + e - r = n - c :=
  sorry

/-- Lemma 42.62.6: Let `k` be a field. Let `X` be a scheme smooth over `k`. Let
`i : Y ⟶ X` be a regular closed immersion. Let `alpha` be in `CH_*(X)`. If `Y` is
equidimensional of dimension `e`, then `alpha · [Y]_e = i_*(i!(alpha))` in `CH_*(X)`,
where the product is the cap of the Chow exterior product by the canonical Gysin class of
the diagonal, `[Y]_e` is the proper pushforward of the fundamental class of `Y`, and `i!`
is the closed Gysin class of `i`. -/
@[stacks 0FFE]
theorem intersectionProduct_eq_pushforward_gysin
    (X : SchemeOverField k) [Smooth X.hom] {Y : SchemeOverField k} (i : Y ⟶ X)
    [IsRegularClosedImmersion i.left] (e : ℕ) [RelativeDimension Y.hom e]
    (r : ℕ) [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (DΔ : DiagonalSpecialization X r)
    (c : ℕ) [IsFiniteLocallyFreeOfRank c (conormalSheaf i.left)]
    (Di : ClosedSpecialization (fun _ ↦ 0) Y.hom X.hom i.left (Over.w i)
      (ofNormalSheaf i.left c (bidualityIso i.left c)))
    (hcodim : r = c + e) {n : ℤ} (alpha : RelativeChow (fun _ ↦ 0) X n) :
    intersectionProduct X r DΔ alpha
        (map (fun _ ↦ 0) Y X i e (relativeFundamentalClass Y e)) =
      castRelativeDegree (fun _ ↦ 0)
        (intersectionProduct_gysin_degree n r e c hcodim).symm
        (map (fun _ ↦ 0) Y X i (n - c)
          ((overHom_eq_over i ▸
              globalClassOfRank (fun _ ↦ 0) Y.hom X.hom i.left (Over.w i)
                (ofNormalSheaf i.left c (bidualityIso i.left c)) Di c).cap
            (𝟙 Y) i (𝟙 X) IsPullback.of_id_fst n alpha)) :=
  sorry

namespace Total

/-- The identity of Lemma 42.62.6 on total Chow homology `CH_*(X)`, comparing the
diagonal Gysin cap of the exterior product against `i_*[Y]_e` with the proper pushforward
of the closed Gysin cap `i!(alpha)`. -/
theorem intersectionProduct_eq_pushforward_gysin_total
    (X : SchemeOverField k) [Smooth X.hom] {Y : SchemeOverField k} (i : Y ⟶ X)
    [IsRegularClosedImmersion i.left] (e : ℕ) [RelativeDimension Y.hom e]
    (r : ℕ) [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (DΔ : DiagonalSpecialization X r)
    (c : ℕ) [IsFiniteLocallyFreeOfRank c (conormalSheaf i.left)]
    (Di : ClosedSpecialization (fun _ ↦ 0) Y.hom X.hom i.left (Over.w i)
      (ofNormalSheaf i.left c (bidualityIso i.left c)))
    (hcodim : r = c + e) (alpha : Total (fun _ ↦ 0) X) :
    totalCap (fun _ ↦ 0) (diagonalGysinClass X r DΔ)
        (𝟙 X) (diagonal X) (𝟙 (X ⨯ X)) IsPullback.of_id_fst
        (exteriorProduct X X alpha
          (map (fun _ ↦ 0) i
            (DirectSum.of _ (e : ℤ) (relativeFundamentalClass Y e)))) =
      map (fun _ ↦ 0) i
        (totalCap (fun _ ↦ 0)
          (overHom_eq_over i ▸
            globalClassOfRank (fun _ ↦ 0) Y.hom X.hom i.left (Over.w i)
              (ofNormalSheaf i.left c (bidualityIso i.left c)) Di c)
          (𝟙 Y) i (𝟙 X) IsPullback.of_id_fst alpha) :=
  sorry

end Total

end AlgebraicGeometry.ChowGroup
