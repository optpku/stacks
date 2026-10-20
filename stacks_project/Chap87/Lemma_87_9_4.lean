module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.FactorThroughStage
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

/- Lemma 87.9.4 -/
@[stacks 0AIA] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.exists_factorThroughStage :
    ∀ {S : Scheme.{u}} {Λ : Type v} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
      (D : Λ ⥤ Over S) {X : (Over S)ᵒᵖ ⥤ Type u}
      (hcolim : AlgebraicGeometry.FormalAlgebraicSpace.IsDirectedAffineThickeningColimit D X)
      (c : Cocone (D ⋙ yoneda)) (hc : IsColimit c) (η : c.pt ⟶ X)
      (hη_surj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η)
      (hη_inj : Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η)
      (h_presentation : ∃ (U R : Over S) (π : yoneda.obj U ⟶ X)
        (σ : yoneda.obj R ⟶ pullback π π),
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) π ∧
          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) σ)
      {Y : AlgebraicSpace S} [AlgebraicSpace.IsQuasiCompact Y]
      (f : Y.functorOfPoints ⟶ X),
      ∃ (i : Λ) (g : Y.functorOfPoints ⟶ yoneda.obj (D.obj i)),
        g ≫ c.ι.app i ≫ η = f)
