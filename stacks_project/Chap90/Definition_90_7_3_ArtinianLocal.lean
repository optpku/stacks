module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Artinian local algebras with residue identification

Objects of the base category `C_Λ` are Artinian local `Λ`-algebras equipped with a
`Λ`-algebra identification of the residue field with a fixed finite `Λ`-field `k`.
Morphisms are local `Λ`-algebra maps compatible with those identifications.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- An Artinian local `Λ`-algebra with a chosen identification of its residue field with `k`. -/
structure ArtinianLocalAlgCat where
  /-- Underlying algebra. -/
  carrier : Type u
  [commRing : CommRing carrier]
  [algebra : Algebra Λ carrier]
  [isLocalRing : IsLocalRing carrier]
  [isArtinianRing : IsArtinianRing carrier]
  /-- Residue-field identification `ResidueField carrier ≃ₐ[Λ] k`. -/
  residueFieldIso : ResidueField carrier ≃ₐ[Λ] k

attribute [instance] ArtinianLocalAlgCat.commRing ArtinianLocalAlgCat.algebra
  ArtinianLocalAlgCat.isLocalRing ArtinianLocalAlgCat.isArtinianRing

namespace ArtinianLocalAlgCat

variable {Λ k}

/-- Bundle an Artinian local `Λ`-algebra together with a residue identification to `k`. -/
def of (X : Type u) [CommRing X] [Algebra Λ X] [IsLocalRing X] [IsArtinianRing X]
    (residueFieldIso : ResidueField X ≃ₐ[Λ] k) : ArtinianLocalAlgCat Λ k where
  carrier := X
  residueFieldIso := residueFieldIso

/-- The bundled object recovers the supplied carrier. -/
theorem of_carrier (X : Type u) [CommRing X] [Algebra Λ X] [IsLocalRing X] [IsArtinianRing X]
    (residueFieldIso : ResidueField X ≃ₐ[Λ] k) :
    (of X residueFieldIso).carrier = X := sorry

/-- A morphism of residue-identified Artinian local `Λ`-algebras is a local algebra map
compatible with the residue identifications. -/
structure Hom (A B : ArtinianLocalAlgCat Λ k) where
  /-- Underlying `Λ`-algebra homomorphism. -/
  hom : A.carrier →ₐ[Λ] B.carrier
  [isLocalHom : IsLocalHom hom]
  /-- The residue identification of `B` after `hom` recovers that of `A`. -/
  residue_compat :
    B.residueFieldIso.toAlgHom.comp (ResidueField.mapAlgHom hom) = A.residueFieldIso.toAlgHom

attribute [instance] Hom.isLocalHom

/-- Identity morphism of a residue-identified Artinian local algebra. -/
def Hom.id (A : ArtinianLocalAlgCat Λ k) : Hom A A where
  hom := AlgHom.id Λ A.carrier
  isLocalHom := sorry
  residue_compat := sorry

/-- Composition of residue-compatible local algebra maps. -/
def Hom.comp {A B C : ArtinianLocalAlgCat Λ k} (f : Hom A B) (g : Hom B C) : Hom A C where
  hom := g.hom.comp f.hom
  isLocalHom := sorry
  residue_compat := sorry

/-- The identity morphism is the identity algebra map. -/
theorem Hom.id_hom (A : ArtinianLocalAlgCat Λ k) :
    (Hom.id A).hom = AlgHom.id Λ A.carrier := sorry

/-- Composition of morphisms is composition of algebra maps. -/
theorem Hom.comp_hom {A B C : ArtinianLocalAlgCat Λ k} (f : Hom A B) (g : Hom B C) :
    (Hom.comp f g).hom = g.hom.comp f.hom := sorry

/-- Morphisms are precisely local `Λ`-algebra maps compatible with residue identifications. -/
theorem hom_spec {A B : ArtinianLocalAlgCat Λ k} (f : Hom A B) :
    IsLocalHom f.hom ∧
      B.residueFieldIso.toAlgHom.comp (ResidueField.mapAlgHom f.hom) =
        A.residueFieldIso.toAlgHom := sorry

/-- Category of Artinian local `Λ`-algebras with residue identification to `k`. -/
instance category : Category.{u} (ArtinianLocalAlgCat Λ k) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp f g
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

end ArtinianLocalAlgCat
