module

public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import ReasLib.RingTheory.Completion.LocalRing
public import stacks_project.Chap90.Definition_90_7_3_ArtinianLocal

/-!
# Complete local algebras with residue identification

Objects of the completed base category `Ĉ_Λ` are Noetherian complete local `Λ`-algebras
equipped with a residue identification to `k`. Truncation sends `R` to
`R ⧸ maximalIdeal R ^ (n + 1)` in `C_Λ`.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- A Noetherian complete local `Λ`-algebra with a chosen identification of its residue
field with `k`. -/
structure CompleteLocalAlgCat where
  /-- Underlying algebra. -/
  carrier : Type u
  [commRing : CommRing carrier]
  [algebra : Algebra Λ carrier]
  [isLocalRing : IsLocalRing carrier]
  [isNoetherianRing : IsNoetherianRing carrier]
  [isCompleteLocalRing : IsCompleteLocalRing carrier]
  /-- Residue-field identification `ResidueField carrier ≃ₐ[Λ] k`. -/
  residueFieldIso : ResidueField carrier ≃ₐ[Λ] k

attribute [instance] CompleteLocalAlgCat.commRing CompleteLocalAlgCat.algebra
  CompleteLocalAlgCat.isLocalRing CompleteLocalAlgCat.isNoetherianRing
  CompleteLocalAlgCat.isCompleteLocalRing

namespace CompleteLocalAlgCat

variable {Λ k}

/-- Bundle a Noetherian complete local `Λ`-algebra together with a residue identification
to `k`. -/
def of (X : Type u) [CommRing X] [Algebra Λ X] [IsNoetherianRing X]
    [IsCompleteLocalRing X] (residueFieldIso : ResidueField X ≃ₐ[Λ] k) :
    CompleteLocalAlgCat Λ k where
  carrier := X
  residueFieldIso := residueFieldIso

/-- The bundled object recovers the supplied carrier. -/
theorem of_carrier (X : Type u) [CommRing X] [Algebra Λ X] [IsNoetherianRing X]
    [IsCompleteLocalRing X] (residueFieldIso : ResidueField X ≃ₐ[Λ] k) :
    (of X residueFieldIso).carrier = X := sorry

/-- A morphism of residue-identified complete local `Λ`-algebras is a local algebra map
compatible with the residue identifications. -/
structure Hom (A B : CompleteLocalAlgCat Λ k) where
  /-- Underlying `Λ`-algebra homomorphism. -/
  hom : A.carrier →ₐ[Λ] B.carrier
  [isLocalHom : IsLocalHom hom]
  /-- The residue identification of `B` after `hom` recovers that of `A`. -/
  residue_compat :
    B.residueFieldIso.toAlgHom.comp (ResidueField.mapAlgHom hom) = A.residueFieldIso.toAlgHom

attribute [instance] Hom.isLocalHom

/-- Identity morphism of a residue-identified complete local algebra. -/
def Hom.id (A : CompleteLocalAlgCat Λ k) : Hom A A where
  hom := AlgHom.id Λ A.carrier
  isLocalHom := sorry
  residue_compat := sorry

/-- Composition of residue-compatible local algebra maps. -/
def Hom.comp {A B C : CompleteLocalAlgCat Λ k} (f : Hom A B) (g : Hom B C) : Hom A C where
  hom := g.hom.comp f.hom
  isLocalHom := sorry
  residue_compat := sorry

/-- The identity morphism is the identity algebra map. -/
theorem Hom.id_hom (A : CompleteLocalAlgCat Λ k) :
    (Hom.id A).hom = AlgHom.id Λ A.carrier := sorry

/-- Composition of morphisms is composition of algebra maps. -/
theorem Hom.comp_hom {A B C : CompleteLocalAlgCat Λ k} (f : Hom A B) (g : Hom B C) :
    (Hom.comp f g).hom = g.hom.comp f.hom := sorry

/-- Morphisms are precisely local `Λ`-algebra maps compatible with residue identifications. -/
theorem hom_spec {A B : CompleteLocalAlgCat Λ k} (f : Hom A B) :
    IsLocalHom f.hom ∧
      B.residueFieldIso.toAlgHom.comp (ResidueField.mapAlgHom f.hom) =
        A.residueFieldIso.toAlgHom := sorry

/-- Category of Noetherian complete local `Λ`-algebras with residue identification to `k`. -/
instance category : Category.{u} (CompleteLocalAlgCat Λ k) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp f g
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The quotient of a local ring by a positive power of its maximal ideal is nontrivial. -/
instance instNontrivial_quotient_maximalIdeal_pow (R : Type u) [CommRing R] [IsLocalRing R]
    (n : ℕ) : Nontrivial (R ⧸ maximalIdeal R ^ (n + 1)) :=
  Ideal.Quotient.nontrivial_iff.mpr
    (mt
      (fun h ↦
        eq_top_iff.2 (h.symm.trans_le (Ideal.pow_le_self (Nat.succ_ne_zero n))))
      (Ideal.IsMaximal.ne_top inferInstance))

/-- The quotient of a local ring by a positive power of its maximal ideal is local. -/
instance instIsLocalRing_quotient_maximalIdeal_pow (R : Type u) [CommRing R] [IsLocalRing R]
    (n : ℕ) : IsLocalRing (R ⧸ maximalIdeal R ^ (n + 1)) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- The quotient of a Noetherian local ring by a positive power of its maximal ideal is
Artinian. -/
instance instIsArtinianRing_quotient_maximalIdeal_pow (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (n : ℕ) :
    IsArtinianRing (R ⧸ maximalIdeal R ^ (n + 1)) := sorry

/-- Canonical residue identification of a maximal-adic truncation with the residue field of
the original complete local algebra. -/
noncomputable def truncationResidueFieldIso (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    ResidueField (R.carrier ⧸ maximalIdeal R.carrier ^ (n + 1)) ≃ₐ[Λ] k :=
  (Ideal.quotientEquivAlgOfEq Λ
      (IsLocalRing.map_maximalIdeal_of_surjective
        (Ideal.Quotient.mk (maximalIdeal R.carrier ^ (n + 1)))
        Ideal.Quotient.mk_surjective).symm).trans
    ((DoubleQuot.quotQuotEquivQuotOfLEₐ Λ
        (Ideal.pow_le_self (Nat.succ_ne_zero n))).trans R.residueFieldIso)

/-- The `n`th maximal-adic truncation `R ⧸ maximalIdeal R ^ (n + 1)`, viewed in `C_Λ`. -/
noncomputable def truncation (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    ArtinianLocalAlgCat Λ k :=
  ArtinianLocalAlgCat.of (R.carrier ⧸ maximalIdeal R.carrier ^ (n + 1))
    (truncationResidueFieldIso R n)

/-- The carrier of a truncation is the corresponding maximal-adic quotient. -/
theorem truncation_carrier (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    (R.truncation n).carrier = (R.carrier ⧸ maximalIdeal R.carrier ^ (n + 1)) := sorry

/-- A truncation is Artinian local and residue-identified with `k`. -/
theorem truncation_spec (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    IsArtinianRing (R.truncation n).carrier ∧
      IsLocalRing (R.truncation n).carrier ∧
      (R.truncation n).residueFieldIso = R.truncationResidueFieldIso n := sorry

/-- Canonical projection `R ⧸ m^{n+2} ⟶ R ⧸ m^{n+1}` of successive truncations. -/
noncomputable def truncationMap (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    ArtinianLocalAlgCat.Hom (R.truncation (n + 1)) (R.truncation n) where
  hom := Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))
  isLocalHom := sorry
  residue_compat := sorry

/-- The underlying algebra map of a truncation projection is the canonical factor map. -/
theorem truncationMap_hom (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    (R.truncationMap n).hom =
      Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) := sorry


end CompleteLocalAlgCat
