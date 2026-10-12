/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.Topology.Defs.Basic
public import stacks_project.Chap100.Lemma_100_7_4_Points
public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact
public import stacks_project.Chap101.Definition_101_13_2_Closed

/-!
# Affine finite-presentation approximation of closed subsets

A quasi-compact morphism from a quasi-compact algebraic stack to an affine
scheme admits affine finite-presentation approximations of closed subsets of a
fibre product that avoid a given point of an affine base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Bicategory
open FiberedCategoryOver.Groupoids (overMap)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The 2-fibre product `𝒳 ×_Y Z` of a morphism of algebraic stacks with the
slice morphism induced by a scheme morphism over `S`. -/
abbrev pullbackAlongOver {S : Scheme.{u}} {X : GroupoidsOver S} {Y Z : Over S}
    (f : X ⟶ GroupoidsOver.slice Y) (g : Z ⟶ Y) : GroupoidsOver S :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u} f (overMap g)

/-- The first projection `𝒳 ×_Y Z ⟶ 𝒳`. -/
abbrev pullbackAlongOver.fst {S : Scheme.{u}} {X : GroupoidsOver S}
    {Y Z : Over S} (f : X ⟶ GroupoidsOver.slice Y) (g : Z ⟶ Y) :
    pullbackAlongOver f g ⟶ X :=
  TwoFibreProduct.fst.{u + 1, u, u + 1, u} f (overMap g)

/-- The second projection `𝒳 ×_Y Z ⟶ Z`. -/
abbrev pullbackAlongOver.snd {S : Scheme.{u}} {X : GroupoidsOver S}
    {Y Z : Over S} (f : X ⟶ GroupoidsOver.slice Y) (g : Z ⟶ Y) :
    pullbackAlongOver f g ⟶ GroupoidsOver.slice Z :=
  TwoFibreProduct.snd.{u + 1, u, u + 1, u} f (overMap g)

/-- Lemma 102.7.1: Let `g : Z ⟶ Y` be a morphism of affine schemes, and let
`f : 𝒳 ⟶ Y` be a quasi-compact morphism of algebraic stacks. Let `z ∈ Z` and let
`T ⊂ |𝒳 ×_Y Z|` be a closed subset with `z` not in the image of `T` in `|Z|`.
If `𝒳` is quasi-compact, then there exist an open neighbourhood `V ⊂ Z` of `z`,
a commutative diagram `V ⟶ Z'` over `Z ⟶ Y`, and a closed subset
`T' ⊂ |𝒳 ×_Y Z'|` such that `Z'` is an affine scheme of finite presentation over
`Y`, the image `a(z)` avoids the image of `T'` in `|Z'|`, and the inverse image
of `T` in `|𝒳 ×_Y V|` maps into `T'` along `|𝒳 ×_Y V| ⟶ |𝒳 ×_Y Z'|`. -/
@[stacks 0H29]
theorem existsAffineOpenApproximationAvoidingImage
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] [IsQuasiCompact X]
    {Y Z : Over S} [IsAffine Y.left] [IsAffine Z.left]
    (f : X ⟶ GroupoidsOver.slice Y) [QuasiCompact f] (g : Z ⟶ Y)
    [AlgebraicStack (pullbackAlongOver f g)] (z : Z.left)
    (T : Set (Points (pullbackAlongOver f g)))
    {τ : TopologicalSpace (Points (pullbackAlongOver f g))}
    (hτ : IsPointsTopology (pullbackAlongOver f g) τ)
    (hT : @IsClosed (Points (pullbackAlongOver f g)) τ T)
    (hz : Points.ofSlice z ∉ Points.map (pullbackAlongOver.snd f g) '' T) :
    ∃ (V : Z.left.Opens) (hVz : z ∈ (V : Set Z.left)) (_ : IsAffine V.toScheme)
      (Z' : Over S) (_ : IsAffine Z'.left)
      (a : Over.mk (V.ι ≫ Z.hom) ⟶ Z') (b : Z' ⟶ Y)
      (_ : LocallyOfFinitePresentation b.left)
      (_ : CommSq a.left V.ι b.left g.left)
      (φ : Over.mk (V.ι ≫ Z.hom) ⟶ Y)
      (_ : φ = Over.homMk V.ι rfl ≫ g)
      (hXZ' : AlgebraicStack (pullbackAlongOver f b))
      (hXV : AlgebraicStack (pullbackAlongOver f φ))
      (T' : Set (@Points S (pullbackAlongOver f b) hXZ'))
      (_ : ∀ τ' : TopologicalSpace (@Points S (pullbackAlongOver f b) hXZ'),
        @IsPointsTopology S (pullbackAlongOver f b) hXZ' τ' →
          @IsClosed (@Points S (pullbackAlongOver f b) hXZ') τ' T')
      (toXZ : pullbackAlongOver f φ ⟶ pullbackAlongOver f g)
      (toXZ' : pullbackAlongOver f φ ⟶ pullbackAlongOver f b)
      (_ : toXZ ≫ pullbackAlongOver.fst f g ≅
        pullbackAlongOver.fst f φ)
      (_ : toXZ ≫ pullbackAlongOver.snd f g ≅
        pullbackAlongOver.snd f φ ≫ overMap (Over.homMk V.ι rfl))
      (_ : toXZ' ≫ pullbackAlongOver.fst f b ≅
        pullbackAlongOver.fst f φ)
      (_ : toXZ' ≫ pullbackAlongOver.snd f b ≅
        pullbackAlongOver.snd f φ ≫ overMap a),
      Points.ofSlice (a.left ⟨z, hVz⟩) ∉
          (@Points.map S (pullbackAlongOver f b) hXZ' (GroupoidsOver.slice Z')
              inferInstance (pullbackAlongOver.snd f b)) '' T' ∧
        (@Points.map S (pullbackAlongOver f φ) hXV (pullbackAlongOver f b) hXZ'
            toXZ') ''
          ((@Points.map S (pullbackAlongOver f φ) hXV (pullbackAlongOver f g)
              inferInstance toXZ) ⁻¹' T) ⊆ T' :=
  sorry

end AlgebraicGeometry.AlgebraicStack
