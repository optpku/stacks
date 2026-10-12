/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Order.Directed
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap87.Lemma_87_37_4_Completion

/-!
# Recompletion of a formal algebraic space

If `X` is a formal algebraic space, then its completion along a closed subset
of the reduction remains a formal algebraic space.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace (Points)
open CategoryTheory Limits Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- Lemma 87.37.2: Let `S` be a scheme. Let `X` be a formal algebraic space over
`S`, given by an étale jointly surjective atlas of affine formal algebraic
spaces (each presented as a directed colimit of affine schemes along thickening
transitions, compared to the chart by an fppf-local isomorphism out of the
Yoneda presheaf colimit, and satisfying the coequalizer size condition)
together with a coequalizer size condition on `X`. Let
`T ⊆ Points (reduction X)` be a closed subset. Then the functor
`completionAlong X T` on `(Over S)ᵒᵖ ⥤ Type u`, sending `U` to the morphisms
`f : U ⟶ X` with `mapsInto T` (equivalently `f(|U|) ⊆ T`, see
`completionAlong_obj` and `completionAlong.exists_lift`), is a formal algebraic
space: it admits an étale jointly surjective affine atlas of the same shape,
together with the coequalizer size condition. -/
@[stacks 0GVR]
theorem exists_etaleAffineAtlas_completionAlong
    {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [Reduction X]
    {ι : Type u} (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : ∀ i, cover i ⟶ X)
    (h_affine : ∀ i, ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
      (D : Λ ⥤ Over S),
      (∀ a, IsAffine (D.obj a).left) ∧
        (∀ {a b : Λ} (f : a ⟶ b), IsThickening (D.map f).left) ∧
          Presheaf.IsSheaf (Scheme.fppfTopology.over S) (cover i) ∧
            ∃ (c : Cocone (D ⋙ yoneda)) (η : c.pt ⟶ cover i),
              Nonempty (IsColimit c) ∧
                Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η ∧
                  Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η ∧
                    ∃ (U R : Over S) (πU : yoneda.obj U ⟶ cover i)
                      (σ : yoneda.obj R ⟶ pullback πU πU),
                      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) πU ∧
                        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) σ)
    (h_rep : ∀ i, AlgebraicSpace.representableByAlgebraicSpaces (π i))
    (h_etale : ∀ i (ha : AlgebraicSpace.representableByAlgebraicSpaces (π i))
      {U : Over S} (ξ : yoneda.obj U ⟶ X),
      AlgebraicSpace.Etale (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom ha ξ))
    (c : Cofan cover) (hc : IsColimit c)
    (h_surj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (Cofan.IsColimit.desc hc π))
    (U R : Over S) (πU : yoneda.obj U ⟶ X) (σ : yoneda.obj R ⟶ pullback πU πU)
    (hπU : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) πU)
    (hσ : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) σ)
    (T : Closeds (Points (reduction X))) :
    ∃ (ι' : Type u) (cover' : ι' → ((Over S)ᵒᵖ ⥤ Type u))
      (π' : ∀ i, cover' i ⟶ completionAlong X T),
      (∀ i, ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
        (D : Λ ⥤ Over S),
        (∀ a, IsAffine (D.obj a).left) ∧
          (∀ {a b : Λ} (f : a ⟶ b), IsThickening (D.map f).left) ∧
            Presheaf.IsSheaf (Scheme.fppfTopology.over S) (cover' i) ∧
              ∃ (c' : Cocone (D ⋙ yoneda)) (η : c'.pt ⟶ cover' i),
                Nonempty (IsColimit c') ∧
                  Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η ∧
                    Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η ∧
                      ∃ (U R : Over S) (πU : yoneda.obj U ⟶ cover' i)
                        (σ : yoneda.obj R ⟶ pullback πU πU),
                        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) πU ∧
                          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) σ) ∧
        (∀ i, AlgebraicSpace.representableByAlgebraicSpaces (π' i)) ∧
          (∀ i (ha : AlgebraicSpace.representableByAlgebraicSpaces (π' i))
            {U : Over S} (ξ : yoneda.obj U ⟶ completionAlong X T),
            AlgebraicSpace.Etale (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
            (∃ (c' : Cofan cover') (hc' : IsColimit c'),
              Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
                (Cofan.IsColimit.desc hc' π')) ∧
              ∃ (U' R' : Over S) (πU' : yoneda.obj U' ⟶ completionAlong X T)
                (σ' : yoneda.obj R' ⟶ pullback πU' πU'),
                Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) πU' ∧
                  Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) σ' :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
