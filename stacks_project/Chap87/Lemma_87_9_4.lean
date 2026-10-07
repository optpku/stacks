module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Order.Directed
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact

/-!
# Factoring maps from quasi-compact algebraic spaces through affine thickenings

If `X` is presented as a directed colimit of affine schemes along thickening
transitions, as in Definition 87.9.1, then every morphism from a quasi-compact
algebraic space into `X` factors through some stage.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicSpace CategoryTheory Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 87.9.4: Let `D : Λ ⥤ Over S` be a directed system of affine schemes
over `S` with thickening transitions, as in Definition 87.9.1, and let `c` be a
colimit cocone of `D ⋙ yoneda`, so that `X = c.pt` is the colimit of
`yoneda.obj (D.obj i)`. If `Y` is a quasi-compact algebraic space over `S`,
then any morphism `Y.functorOfPoints ⟶ X` factors through
`yoneda.obj (D.obj i)` for some `i`. -/
@[stacks 0AIA]
theorem exists_factorThroughStage
    {S : Scheme.{u}} {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ Over S) (h_affine : ∀ i, IsAffine (D.obj i).left)
    (h_thickening : ∀ {i j : Λ} (f : i ⟶ j), IsThickening (D.map f).left)
    (c : Cocone (D ⋙ yoneda)) (hc : IsColimit c)
    {Y : AlgebraicSpace S} [IsQuasiCompact Y] (f : Y.functorOfPoints ⟶ c.pt) :
    ∃ (i : Λ) (g : Y.functorOfPoints ⟶ yoneda.obj (D.obj i)),
      g ≫ c.ι.app i = f :=
  sorry

/-- A morphism from the Yoneda embedding of a quasi-compact scheme over `S`
into the colimit of a directed affine thickening system factors through some
stage. -/
theorem exists_factorThroughStage_yoneda
    {S : Scheme.{u}} {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ Over S) (h_affine : ∀ i, IsAffine (D.obj i).left)
    (h_thickening : ∀ {i j : Λ} (f : i ⟶ j), IsThickening (D.map f).left)
    (c : Cocone (D ⋙ yoneda)) (hc : IsColimit c)
    {U : Over S} [CompactSpace U.left] (f : yoneda.obj U ⟶ c.pt) :
    ∃ (i : Λ) (g : yoneda.obj U ⟶ yoneda.obj (D.obj i)),
      g ≫ c.ι.app i = f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
