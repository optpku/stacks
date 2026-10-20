module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import ReasLib.RingTheory.Completion.LocalRing
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal

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

namespace CompleteLocalAlgCat

variable {Λ k}

/-- Noetherian complete local `Λ`-algebras with a chosen residue identification to `k`. -/
def _root_.CompleteLocalAlgCat (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ]
    [Field k] [Algebra Λ k] [Module.Finite Λ k] :=
  Σ' carrier : CommRingCat.{u},
    Σ' algebra : Algebra Λ carrier,
      Σ' isLocalRing : IsLocalRing carrier,
        Σ' isNoetherianRing : IsNoetherianRing carrier,
          Σ' isCompleteLocalRing : IsCompleteLocalRing carrier,
            @ResidueField carrier carrier.commRing isLocalRing ≃ₐ[Λ] k

/-- The underlying commutative-ring object of a complete local algebra. -/
def carrier (A : CompleteLocalAlgCat Λ k) : CommRingCat.{u} := A.1

/-- The stored `Λ`-algebra structure of a complete local algebra. -/
def algebra (A : CompleteLocalAlgCat Λ k) : Algebra Λ A.carrier := A.2.1

/-- The stored local-ring structure of a complete local algebra. -/
def isLocalRing (A : CompleteLocalAlgCat Λ k) : IsLocalRing A.carrier := A.2.2.1

/-- The stored Noetherian-ring structure of a complete local algebra. -/
def isNoetherianRing (A : CompleteLocalAlgCat Λ k) : IsNoetherianRing A.carrier := A.2.2.2.1

/-- The stored maximal-adic completeness structure of a complete local algebra. -/
def isCompleteLocalRing (A : CompleteLocalAlgCat Λ k) : IsCompleteLocalRing A.carrier := A.2.2.2.2.1

/-- The chosen residue-field identification of a complete local algebra. -/
def residueFieldIso (A : CompleteLocalAlgCat Λ k) :
    @AlgEquiv Λ (@ResidueField A.carrier A.carrier.commRing A.isLocalRing) k _ _ _
      (@ResidueField.algebra A.carrier A.carrier.commRing A.isLocalRing Λ inferInstance A.algebra)
      inferInstance := A.2.2.2.2.2

/-- Bundle a Noetherian complete local `Λ`-algebra together with a residue identification to `k`. -/
def of (X : Type u) [CommRing X] [Algebra Λ X] [IsNoetherianRing X]
    [IsCompleteLocalRing X] (residueFieldIso : ResidueField X ≃ₐ[Λ] k) : CompleteLocalAlgCat Λ k :=
  ⟨CommRingCat.of X, inferInstance, inferInstance, inferInstance, inferInstance, residueFieldIso⟩

/-- The bundled object recovers the supplied carrier. -/
theorem of_carrier (X : Type u) [CommRing X] [Algebra Λ X] [IsNoetherianRing X]
    [IsCompleteLocalRing X] (residueFieldIso : ResidueField X ≃ₐ[Λ] k) :
    (of X residueFieldIso).carrier = X := sorry

/-- The explicit `Λ`-algebra homomorphism type between complete-local objects. -/
abbrev algebraHom (A B : CompleteLocalAlgCat Λ k) : Type u :=
  @AlgHom Λ A.carrier B.carrier _ _ _ A.algebra B.algebra

/-- The residue-field map associated to a local algebra homomorphism. -/
noncomputable def residueMap {A B : CompleteLocalAlgCat Λ k} (hom : algebraHom A B)
    (isLocalHom : IsLocalHom hom) :
    @AlgHom Λ (@ResidueField A.carrier A.carrier.commRing A.isLocalRing)
      (@ResidueField B.carrier B.carrier.commRing B.isLocalRing) _ _ _
      (@ResidueField.algebra A.carrier A.carrier.commRing A.isLocalRing Λ inferInstance A.algebra)
      (@ResidueField.algebra B.carrier B.carrier.commRing B.isLocalRing Λ inferInstance B.algebra) := by
  exact @ResidueField.mapAlgHom Λ A.carrier B.carrier _ _ A.isLocalRing _ B.isLocalRing A.algebra B.algebra hom
    isLocalHom

/-- The chosen residue-field identification viewed as an algebra homomorphism. -/
noncomputable def residueIsoHom (A : CompleteLocalAlgCat Λ k) :
    @AlgHom Λ (@ResidueField A.carrier A.carrier.commRing A.isLocalRing) k _ _ _
      (@ResidueField.algebra A.carrier A.carrier.commRing A.isLocalRing Λ inferInstance A.algebra) inferInstance := by
  exact @AlgEquiv.toAlgHom Λ (@ResidueField A.carrier A.carrier.commRing A.isLocalRing) k _ _ _
    (@ResidueField.algebra A.carrier A.carrier.commRing A.isLocalRing Λ inferInstance A.algebra) inferInstance
    A.residueFieldIso

/-- The residue compatibility composite associated to a local algebra homomorphism. -/
noncomputable def residueCompat {A B : CompleteLocalAlgCat Λ k} (hom : algebraHom A B)
    (isLocalHom : IsLocalHom hom) :
    @AlgHom Λ (@ResidueField A.carrier A.carrier.commRing A.isLocalRing) k _ _ _
      (@ResidueField.algebra A.carrier A.carrier.commRing A.isLocalRing Λ inferInstance A.algebra) inferInstance :=
  @AlgHom.comp Λ (@ResidueField A.carrier A.carrier.commRing A.isLocalRing)
    (@ResidueField B.carrier B.carrier.commRing B.isLocalRing) k _ _ _ _
    (@ResidueField.algebra A.carrier A.carrier.commRing A.isLocalRing Λ inferInstance A.algebra)
    (@ResidueField.algebra B.carrier B.carrier.commRing B.isLocalRing Λ inferInstance B.algebra) inferInstance
    (residueIsoHom B) (residueMap hom isLocalHom)

/-- A residue-compatible morphism of complete local algebras. -/
def Hom (A B : CompleteLocalAlgCat Λ k) :=
  Σ' hom : algebraHom A B,
    Σ' isLocalHom : IsLocalHom hom, residueCompat hom isLocalHom = residueIsoHom A

/-- The underlying algebra homomorphism of a complete local algebra morphism. -/
def Hom.hom {A B : CompleteLocalAlgCat Λ k} (f : Hom A B) : algebraHom A B := f.1

/-- The localness proof stored in a complete local algebra morphism. -/
def Hom.isLocalHom {A B : CompleteLocalAlgCat Λ k} (f : Hom A B) : IsLocalHom f.hom := f.2.1

/-- The residue compatibility stored in a complete local algebra morphism. -/
def Hom.residue_compat {A B : CompleteLocalAlgCat Λ k} (f : Hom A B) :
    residueCompat f.hom f.isLocalHom = residueIsoHom A := f.2.2

/-- The underlying ring homomorphism of a complete local algebra morphism. -/
abbrev Hom.toRingHom {A B : CompleteLocalAlgCat Λ k} (f : Hom A B) : A.carrier →+* B.carrier :=
  @AlgHom.toRingHom Λ A.carrier B.carrier _ _ _ A.algebra B.algebra f.hom

/-- Bundle a local algebra map compatible with the chosen residue identifications. -/
def Hom.of {A B : CompleteLocalAlgCat Λ k} (hom : algebraHom A B) (isLocalHom : IsLocalHom hom)
    (residue_compat : residueCompat hom isLocalHom = residueIsoHom A) : Hom A B :=
  ⟨hom, isLocalHom, residue_compat⟩

/-- Identity morphism of a residue-identified complete local algebra. -/
def Hom.id (A : CompleteLocalAlgCat Λ k) : Hom A A :=
  ⟨@AlgHom.id Λ A.carrier _ _ A.algebra, sorry, sorry⟩

/-- Composition of residue-compatible local algebra maps. -/
def Hom.comp {A B C : CompleteLocalAlgCat Λ k} (f : Hom A B) (g : Hom B C) : Hom A C :=
  ⟨@AlgHom.comp Λ A.carrier B.carrier C.carrier _ _ _ _ A.algebra B.algebra C.algebra g.hom f.hom,
    sorry, sorry⟩

/-- The identity morphism is the identity algebra map. -/
theorem Hom.id_hom (A : CompleteLocalAlgCat Λ k) :
    (Hom.id A).hom = @AlgHom.id Λ A.carrier _ _ A.algebra := sorry

/-- Composition of morphisms is composition of algebra maps. -/
theorem Hom.comp_hom {A B C : CompleteLocalAlgCat Λ k} (f : Hom A B) (g : Hom B C) :
    (Hom.comp f g).hom =
      @AlgHom.comp Λ A.carrier B.carrier C.carrier _ _ _ _ A.algebra B.algebra C.algebra g.hom f.hom := sorry

/-- Morphisms are local `Λ`-algebra maps compatible with residue identifications. -/
theorem hom_spec {A B : CompleteLocalAlgCat Λ k} (f : Hom A B) :
    IsLocalHom f.hom ∧ residueCompat f.hom f.isLocalHom = residueIsoHom A := sorry

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
    (mt (fun h ↦ eq_top_iff.2 (h.symm.trans_le (Ideal.pow_le_self (Nat.succ_ne_zero n))))
      (Ideal.IsMaximal.ne_top inferInstance))

/-- The quotient of a local ring by a positive power of its maximal ideal is local. -/
instance instIsLocalRing_quotient_maximalIdeal_pow (R : Type u) [CommRing R] [IsLocalRing R]
    (n : ℕ) : IsLocalRing (R ⧸ maximalIdeal R ^ (n + 1)) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- The quotient of a Noetherian local ring by a positive power of its maximal ideal is Artinian. -/
instance instIsArtinianRing_quotient_maximalIdeal_pow (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (n : ℕ) :
    IsArtinianRing (R ⧸ maximalIdeal R ^ (n + 1)) := sorry

/-- The maximal ideal of a complete-local object, with its stored local-ring structure. -/
abbrev maximalIdeal (R : CompleteLocalAlgCat Λ k) : Ideal R.carrier :=
  @IsLocalRing.maximalIdeal R.carrier inferInstance R.isLocalRing

/-- The carrier ring of the `n`th maximal-adic quotient. -/
abbrev truncationCarrier (R : CompleteLocalAlgCat Λ k) (n : ℕ) : Type u :=
  R.carrier ⧸ (maximalIdeal R) ^ (n + 1)

/-- The local-ring property of a maximal-adic quotient. -/
theorem truncationLocalRing (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    IsLocalRing (truncationCarrier R n) := by
  simpa [truncationCarrier, maximalIdeal] using
    (@instIsLocalRing_quotient_maximalIdeal_pow R.carrier R.carrier.commRing R.isLocalRing n)

/-- The induced `Λ`-algebra structure on a maximal-adic quotient. -/
@[reducible] noncomputable def truncationAlgebra (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    Algebra Λ (truncationCarrier R n) := by
  exact @Ideal.Quotient.algebra Λ R.carrier inferInstance inferInstance R.algebra _ inferInstance

/-- Canonical residue identification of a maximal-adic truncation with `k`. -/
noncomputable def truncationResidueFieldIso (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    @AlgEquiv Λ (@ResidueField (truncationCarrier R n) inferInstance (truncationLocalRing R n)) k _ _ _
      (@ResidueField.algebra (truncationCarrier R n) inferInstance (truncationLocalRing R n) Λ inferInstance
        (truncationAlgebra R n)) inferInstance := by
  let quotientResidueFieldIso (S : Type u) [CommRing S] [Algebra Λ S]
      [IsLocalRing S] [IsNoetherianRing S] (I : Ideal S)
      (hI : I ≤ IsLocalRing.maximalIdeal S) [IsLocalRing (S ⧸ I)]
      (residueFieldIso : ResidueField S ≃ₐ[Λ] k) :
      ResidueField (S ⧸ I) ≃ₐ[Λ] k := by
    exact (Ideal.quotientEquivAlgOfEq Λ
        (IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
          Ideal.Quotient.mk_surjective).symm).trans
      ((DoubleQuot.quotQuotEquivQuotOfLEₐ Λ hI).trans residueFieldIso)
  exact @quotientResidueFieldIso R.carrier R.carrier.commRing R.algebra R.isLocalRing
    R.isNoetherianRing (maximalIdeal R ^ (n + 1))
    (Ideal.pow_le_self (Nat.succ_ne_zero n)) (truncationLocalRing R n) R.residueFieldIso

/-- The `n`th maximal-adic truncation, viewed in the Artinian-local category. -/
noncomputable def truncation (R : CompleteLocalAlgCat Λ k) (n : ℕ) : ArtinianLocalAlgCat Λ k := by
  exact ⟨CommRingCat.of (truncationCarrier R n), truncationAlgebra R n, truncationLocalRing R n,
    @instIsArtinianRing_quotient_maximalIdeal_pow R.carrier R.carrier.commRing R.isNoetherianRing
      R.isLocalRing n, truncationResidueFieldIso R n⟩

/-- The carrier of a truncation is the corresponding maximal-adic quotient. -/
theorem truncation_carrier (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    (R.truncation n).carrier = (R.carrier ⧸ (maximalIdeal R) ^ (n + 1)) := sorry

/-- A truncation is Artinian local and residue-identified with `k`. -/
theorem truncation_spec (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    IsArtinianRing (R.truncation n).carrier ∧ IsLocalRing (R.truncation n).carrier ∧
      (R.truncation n).residueFieldIso = R.truncationResidueFieldIso n := sorry

/-- The canonical algebra map between successive maximal-adic quotients. -/
noncomputable def truncationFactor (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    @AlgHom Λ (truncationCarrier R (n + 1)) (truncationCarrier R n) _ _ _
      (truncationAlgebra R (n + 1)) (truncationAlgebra R n) := by
  exact @Ideal.Quotient.factorₐ Λ R.carrier inferInstance inferInstance R.algebra _ _ inferInstance inferInstance
    (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))

/-- Canonical projection between successive truncations. -/
noncomputable def truncationMap (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    ArtinianLocalAlgCat.Hom (R.truncation (n + 1)) (R.truncation n) :=
  ArtinianLocalAlgCat.Hom.of
    (by
      change @AlgHom Λ (truncationCarrier R (n + 1)) (truncationCarrier R n) _ _ _
        (truncationAlgebra R (n + 1)) (truncationAlgebra R n)
      exact truncationFactor R n) sorry sorry

/-- The underlying algebra map of a truncation projection is the canonical factor map. -/
theorem truncationMap_hom (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    (R.truncationMap n).hom =
      truncationFactor R n := sorry

end CompleteLocalAlgCat
