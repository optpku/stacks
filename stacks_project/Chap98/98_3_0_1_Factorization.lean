module

public import ReasLib.AlgebraicGeometry.Scheme.Artinian.ResidueFactorization

@[expose] public section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

variable {S : Scheme.{u}} {k A : Type u} [Field k] [CommRing A] [IsLocalRing A]
  [IsArtinianRing A]
variable {σ : Spec (CommRingCat.of k) ⟶ S}

#check (AlgebraicGeometry.residueSpecMap :
  (ResidueField A ≃+* k) → (Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)))

#check (AlgebraicGeometry.ArtinianResidueFactorization.factor :
  ∀ (F : ArtinianResidueFactorization σ A), residueSpecMap F.residueFieldIso ≫ F.toS = σ)
