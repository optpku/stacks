module

public import ReasLib.AlgebraicGeometry.Scheme.Artinian.Local

/-! Spectra of local Artinian rings and their characterizations. -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

#check (AlgebraicGeometry.IsSpecLocalArtinian :
  ∀ (X : Scheme.{u}),
    Prop)

#check (AlgebraicGeometry.instIsSpecLocalArtinianSpec :
  ∀ {A : Type u} [CommRing A] [IsLocalRing A]
    [IsArtinianRing A],
    IsSpecLocalArtinian (Spec (CommRingCat.of A)))

#check (AlgebraicGeometry.isSpecLocalArtinian_iff :
  ∀ {X : Scheme.{u}},
    IsSpecLocalArtinian X ↔
      IsAffine X ∧ IsArtinianRing Γ(X, ⊤) ∧ IsLocalRing Γ(X, ⊤))

#check (AlgebraicGeometry.isSpecLocalArtinian_iff_exists_iso :
  ∀ {X : Scheme.{u}},
    IsSpecLocalArtinian X ↔
      ∃ (A : Type u) (_ : CommRing A) (_ : IsLocalRing A) (_ : IsArtinianRing A),
        Nonempty (X ≅ Spec (CommRingCat.of A)))
