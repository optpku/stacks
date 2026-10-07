module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Artinian.ResidueFactorization

@[expose] public section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

variable {S : Scheme.{u}} {k A : Type u} [Field k] [CommRing A] [IsLocalRing A]
  [IsArtinianRing A]
variable {σ : Spec (CommRingCat.of k) ⟶ S}

/- 98.3.0.1: the factorization `Spec(k) ⟶ Spec(A) ⟶ S` of `σ`, with `A`
Artinian local and the first arrow induced by a residue-field identification. -/
@[stacks 07T3] #check (AlgebraicGeometry.ArtinianResidueFactorization :
  (Spec (CommRingCat.of k) ⟶ S) → (A : Type u) → [CommRing A] →
    [IsLocalRing A] → [IsArtinianRing A] → Type u)

#check (AlgebraicGeometry.ArtinianResidueFactorization.factor :
  ∀ (F : ArtinianResidueFactorization σ A), residueSpecMap F.residueFieldIso ≫ F.toS = σ)
