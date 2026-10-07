module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Order.Directed
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import stacks_project.Chap87.Lemma_87_37_4_Completion

/-!
# Recompletion of an affine formal algebraic space

If `X` is an affine formal algebraic space, then its completion along a closed
subset of the reduction remains an affine formal algebraic space.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace (Points)
open CategoryTheory Limits Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- Lemma 87.37.1: Let `S` be a scheme. Let `X` be an affine formal algebraic
space over `S`, presented as a directed colimit of affine schemes along
thickening transitions, compared to `X` by an fppf-local isomorphism out of
the Yoneda presheaf colimit, and satisfying the coequalizer size condition.
Let `T ⊆ Points (reduction X)` be a closed subset. Then the functor
`completionAlong X T` on `(Over S)ᵒᵖ ⥤ Type u`, sending `U` to the morphisms
`f : U ⟶ X` with `mapsInto T` (equivalently `f(|U|) ⊆ T`, see
`completionAlong_obj` and `completionAlong.exists_lift`), is again an affine
formal algebraic space: it admits a directed affine thickening presentation
with an fppf-local isomorphism from the Yoneda presheaf colimit, together with
the coequalizer size condition. -/
@[stacks 0GVQ]
theorem exists_directedAffineThickeningColimit_completionAlong
    {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [Reduction X]
    {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] (D : Λ ⥤ Over S)
    (h_affine : ∀ i, IsAffine (D.obj i).left)
    (h_thickening : ∀ {i j : Λ} (f : i ⟶ j), IsThickening (D.map f).left)
    (c : Cocone (D ⋙ yoneda)) (hc : IsColimit c) (η : c.pt ⟶ X)
    (hη_surj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η)
    (hη_inj : Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η)
    (U R : Over S) (πU : yoneda.obj U ⟶ X) (σ : yoneda.obj R ⟶ pullback πU πU)
    (hπU : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) πU)
    (hσ : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) σ)
    (T : Closeds (Points (reduction X))) :
    ∃ (Λ' : Type u) (_ : Preorder Λ') (_ : IsDirected Λ' (· ≤ ·))
      (D' : Λ' ⥤ Over S),
      (∀ i, IsAffine (D'.obj i).left) ∧
        (∀ {i j : Λ'} (f : i ⟶ j), IsThickening (D'.map f).left) ∧
          ∃ (c' : Cocone (D' ⋙ yoneda)) (η' : c'.pt ⟶ completionAlong X T),
            Nonempty (IsColimit c') ∧
              Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η' ∧
                Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η' ∧
                  ∃ (U' R' : Over S)
                    (πU' : yoneda.obj U' ⟶ completionAlong X T)
                    (σ' : yoneda.obj R' ⟶ pullback πU' πU'),
                    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) πU' ∧
                      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) σ' :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
