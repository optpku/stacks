module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.WithSection.IsoClasses

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/- Projection of section-rigidified invertible modules to schemes over the base. -/
#check (AlgebraicGeometry.AlgebraicSpace.Picard.WithSection.p :
  ∀ (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B),
    Picard.WithSection.Obj f σ hσ ⥤ Over S)

/- Pullback on Picard groups along the base-changed section. -/
#check (AlgebraicGeometry.AlgebraicSpace.Picard.WithSection.sectionPicard :
  ∀ (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B) (τ : CohStack.SchemesOver B),
    (CohStack.fiber f τ).PicardGroup →+ (ofOver τ.left).PicardGroup)
