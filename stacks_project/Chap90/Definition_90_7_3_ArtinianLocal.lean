module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal

/-! Compatibility checks for the Artinian local algebra category. -/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

#check (ArtinianLocalAlgCat.of_carrier :
  ∀ (X : Type u) [CommRing X] [Algebra Λ X] [IsLocalRing X] [IsArtinianRing X]
    (residueFieldIso : ResidueField X ≃ₐ[Λ] k),
    (ArtinianLocalAlgCat.of X residueFieldIso).carrier = X)

#check (ArtinianLocalAlgCat.Hom.comp_hom :
  ∀ {A B C : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) (g : B ⟶ C),
    (ArtinianLocalAlgCat.Hom.comp f g).hom =
      @AlgHom.comp Λ A.carrier B.carrier C.carrier _ _ _ _ A.algebra B.algebra C.algebra g.hom f.hom)
