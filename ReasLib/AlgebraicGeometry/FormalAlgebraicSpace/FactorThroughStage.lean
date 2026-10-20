/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Basic

/-!
# Factorization through a stage of a formal algebraic space

Morphisms from quasi-compact algebraic spaces into a directed affine
thickening colimit factor through one of the affine stages.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- Let `X ≅ colim X_λ` be a nonempty directed affine thickening colimit, presented by
the given colimit cocone `c` of the Yoneda diagram together with the given fppf-local
isomorphism `η : c.pt ⟶ X`, and assume the set-theoretic condition (a presentation of
`X` as a quotient of representables). Then any morphism from a quasi-compact algebraic
space into `X` factors through the structure map `X_λ ⟶ X` of this presentation for
some `λ`. -/
theorem exists_factorThroughStage
    {S : Scheme.{u}} {Λ : Type v} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (D : Λ ⥤ Over S) {X : (Over S)ᵒᵖ ⥤ Type u}
    (hcolim : IsDirectedAffineThickeningColimit D X)
    (c : Cocone (D ⋙ yoneda)) (hc : IsColimit c) (η : c.pt ⟶ X)
    (hη_surj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η)
    (hη_inj : Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η)
    (h_presentation : ∃ (U R : Over S) (π : yoneda.obj U ⟶ X)
      (σ : yoneda.obj R ⟶ pullback π π),
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) π ∧
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) σ)
    {Y : AlgebraicSpace S} [AlgebraicSpace.IsQuasiCompact Y]
    (f : Y.functorOfPoints ⟶ X) :
    ∃ (i : Λ) (g : Y.functorOfPoints ⟶ yoneda.obj (D.obj i)),
      g ≫ c.ι.app i ≫ η = f := sorry

end AlgebraicGeometry.FormalAlgebraicSpace
