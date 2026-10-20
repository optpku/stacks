module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.AdicStarLocalMorphismProperty

/-! # Affine étale tests of adic-star morphism properties -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

universe u v

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicStarRing B],
    (B →+* A) → Prop)
variable (f : X ⟶ Y)

#check (AlgebraicGeometry.IsLocallyAdicStar.etaleAffineLocally P : (X ⟶ Y) → Prop)
#check (AlgebraicGeometry.IsLocallyAdicStar.existsCoverOnTarget P : (X ⟶ Y) → Prop)
#check (AlgebraicGeometry.IsLocallyAdicStar.existsCoverOnSource P : (X ⟶ Y) → Prop)
