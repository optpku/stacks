/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.RingTheory.Completion.LocalRing

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

namespace ArtinianLocalAlgCat

variable {Λ k}

/-- Artinian local `Λ`-algebras with a chosen identification of their residue field to `k`. -/
def _root_.ArtinianLocalAlgCat (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ]
    [Field k] [Algebra Λ k] [Module.Finite Λ k] :=
  Σ' carrier : CommRingCat.{u},
    Σ' algebra : Algebra Λ carrier,
      Σ' isLocalRing : IsLocalRing carrier,
        Σ' isArtinianRing : IsArtinianRing carrier,
          @AlgEquiv Λ (@ResidueField carrier carrier.commRing isLocalRing) k _ _ _
            (@ResidueField.algebra carrier carrier.commRing isLocalRing Λ inferInstance algebra)
            inferInstance

/-- The underlying commutative-ring object of an Artinian local algebra. -/
def carrier (A : ArtinianLocalAlgCat Λ k) : CommRingCat.{u} := A.1

/-- The stored `Λ`-algebra structure of an Artinian local algebra. -/
def algebra (A : ArtinianLocalAlgCat Λ k) : Algebra Λ A.carrier := A.2.1

/-- The stored local-ring structure of an Artinian local algebra. -/
def isLocalRing (A : ArtinianLocalAlgCat Λ k) : IsLocalRing A.carrier := A.2.2.1

/-- The stored Artinian-ring structure of an Artinian local algebra. -/
def isArtinianRing (A : ArtinianLocalAlgCat Λ k) : IsArtinianRing A.carrier := A.2.2.2.1

/-- The chosen residue-field identification of an Artinian local algebra. -/
def residueFieldIso (A : ArtinianLocalAlgCat Λ k) :
    @AlgEquiv Λ (@ResidueField A.carrier A.carrier.commRing A.isLocalRing) k _ _ _
      (@ResidueField.algebra A.carrier A.carrier.commRing A.isLocalRing Λ inferInstance A.algebra)
      inferInstance := A.2.2.2.2

/-- Bundle an Artinian local `Λ`-algebra together with a residue identification to `k`. -/
def of (X : Type u) [CommRing X] [Algebra Λ X] [IsLocalRing X] [IsArtinianRing X]
    (residueFieldIso : ResidueField X ≃ₐ[Λ] k) : ArtinianLocalAlgCat Λ k :=
  ⟨CommRingCat.of X, inferInstance, inferInstance, inferInstance, residueFieldIso⟩

/-- The bundled object recovers the supplied carrier. -/
theorem of_carrier (X : Type u) [CommRing X] [Algebra Λ X] [IsLocalRing X] [IsArtinianRing X]
    (residueFieldIso : ResidueField X ≃ₐ[Λ] k) :
    (of X residueFieldIso).carrier = X := sorry

/-- The explicit `Λ`-algebra homomorphism type using the stored structures. -/
abbrev algebraHom (A B : ArtinianLocalAlgCat Λ k) : Type u :=
  @AlgHom Λ A.carrier B.carrier _ _ _ A.algebra B.algebra

/-- The residue-field map associated to a local algebra homomorphism. -/
noncomputable def residueMap {A B : ArtinianLocalAlgCat Λ k} (hom : algebraHom A B)
    (isLocalHom : IsLocalHom hom) :
    @AlgHom Λ (@ResidueField A.carrier A.carrier.commRing A.isLocalRing)
      (@ResidueField B.carrier B.carrier.commRing B.isLocalRing) _ _ _
      (@ResidueField.algebra A.carrier A.carrier.commRing A.isLocalRing Λ inferInstance A.algebra)
      (@ResidueField.algebra B.carrier B.carrier.commRing B.isLocalRing Λ inferInstance B.algebra) := by
  exact @ResidueField.mapAlgHom Λ A.carrier B.carrier _ _ A.isLocalRing _ B.isLocalRing A.algebra B.algebra hom
    isLocalHom

/-- The chosen residue-field identification viewed as an algebra homomorphism. -/
noncomputable def residueIsoHom (A : ArtinianLocalAlgCat Λ k) :
    @AlgHom Λ (@ResidueField A.carrier A.carrier.commRing A.isLocalRing) k _ _ _
      (@ResidueField.algebra A.carrier A.carrier.commRing A.isLocalRing Λ inferInstance A.algebra) inferInstance := by
  exact @AlgEquiv.toAlgHom Λ (@ResidueField A.carrier A.carrier.commRing A.isLocalRing) k _ _ _
    (@ResidueField.algebra A.carrier A.carrier.commRing A.isLocalRing Λ inferInstance A.algebra) inferInstance
    A.residueFieldIso

/-- The residue compatibility composite associated to a local algebra homomorphism. -/
noncomputable def residueCompat {A B : ArtinianLocalAlgCat Λ k} (hom : algebraHom A B)
    (isLocalHom : IsLocalHom hom) :
    @AlgHom Λ (@ResidueField A.carrier A.carrier.commRing A.isLocalRing) k _ _ _
      (@ResidueField.algebra A.carrier A.carrier.commRing A.isLocalRing Λ inferInstance A.algebra) inferInstance :=
  @AlgHom.comp Λ (@ResidueField A.carrier A.carrier.commRing A.isLocalRing)
    (@ResidueField B.carrier B.carrier.commRing B.isLocalRing) k _ _ _ _
    (@ResidueField.algebra A.carrier A.carrier.commRing A.isLocalRing Λ inferInstance A.algebra)
    (@ResidueField.algebra B.carrier B.carrier.commRing B.isLocalRing Λ inferInstance B.algebra) inferInstance
    (residueIsoHom B) (residueMap hom isLocalHom)

/-- A residue-compatible morphism of Artinian local algebras. -/
def Hom (A B : ArtinianLocalAlgCat Λ k) :=
  Σ' hom : algebraHom A B,
    Σ' isLocalHom : IsLocalHom hom, residueCompat hom isLocalHom = residueIsoHom A

/-- The underlying algebra homomorphism of an Artinian local algebra morphism. -/
def Hom.hom {A B : ArtinianLocalAlgCat Λ k} (f : Hom A B) : algebraHom A B := f.1

/-- The localness proof stored in an Artinian local algebra morphism. -/
abbrev Hom.isLocalHom {A B : ArtinianLocalAlgCat Λ k} (f : Hom A B) : IsLocalHom f.hom := f.2.1

/-- The residue compatibility stored in an Artinian local algebra morphism. -/
theorem Hom.residue_compat {A B : ArtinianLocalAlgCat Λ k} (f : Hom A B) :
    residueCompat f.hom f.isLocalHom = residueIsoHom A := f.2.2

/-- The underlying ring homomorphism of an Artinian local algebra morphism. -/
abbrev Hom.toRingHom {A B : ArtinianLocalAlgCat Λ k} (f : Hom A B) : A.carrier →+* B.carrier :=
  @AlgHom.toRingHom Λ A.carrier B.carrier _ _ _ A.algebra B.algebra f.hom

/-- Bundle a local algebra map compatible with the chosen residue identifications. -/
def Hom.of {A B : ArtinianLocalAlgCat Λ k} (hom : algebraHom A B)
    (isLocalHom : IsLocalHom hom)
    (residue_compat : residueCompat hom isLocalHom = residueIsoHom A) : Hom A B :=
  ⟨hom, isLocalHom, residue_compat⟩

/-- The identity algebra map of an Artinian local algebra is local. -/
theorem Hom.id_isLocalHom (A : ArtinianLocalAlgCat Λ k) :
    IsLocalHom (@AlgHom.id Λ A.carrier _ _ A.algebra) := sorry

/-- The identity algebra map preserves the chosen residue identification. -/
theorem Hom.id_residue_compat (A : ArtinianLocalAlgCat Λ k) :
    residueCompat (@AlgHom.id Λ A.carrier _ _ A.algebra) (Hom.id_isLocalHom A) =
      residueIsoHom A := sorry

/-- Identity morphism of a residue-identified Artinian local algebra. -/
def Hom.id (A : ArtinianLocalAlgCat Λ k) : Hom A A :=
  ⟨@AlgHom.id Λ A.carrier _ _ A.algebra, Hom.id_isLocalHom A, Hom.id_residue_compat A⟩

/-- The composite of two local algebra morphisms of Artinian local algebras is local. -/
theorem Hom.comp_isLocalHom {A B C : ArtinianLocalAlgCat Λ k} (f : Hom A B) (g : Hom B C) :
    IsLocalHom
      (@AlgHom.comp Λ A.carrier B.carrier C.carrier _ _ _ _ A.algebra B.algebra C.algebra
        g.hom f.hom) := sorry

/-- The composite of residue-compatible local algebra maps preserves residue identifications. -/
theorem Hom.comp_residue_compat {A B C : ArtinianLocalAlgCat Λ k}
    (f : Hom A B) (g : Hom B C) :
    residueCompat
      (@AlgHom.comp Λ A.carrier B.carrier C.carrier _ _ _ _ A.algebra B.algebra C.algebra
        g.hom f.hom) (Hom.comp_isLocalHom f g) = residueIsoHom A := sorry

/-- Composition of residue-compatible local algebra maps. -/
def Hom.comp {A B C : ArtinianLocalAlgCat Λ k} (f : Hom A B) (g : Hom B C) : Hom A C :=
  ⟨@AlgHom.comp Λ A.carrier B.carrier C.carrier _ _ _ _ A.algebra B.algebra C.algebra g.hom f.hom,
    Hom.comp_isLocalHom f g, Hom.comp_residue_compat f g⟩

/-- The identity morphism is the identity algebra map. -/
theorem Hom.id_hom (A : ArtinianLocalAlgCat Λ k) :
    (Hom.id A).hom = @AlgHom.id Λ A.carrier _ _ A.algebra := sorry

/-- Composition of morphisms is composition of algebra maps. -/
theorem Hom.comp_hom {A B C : ArtinianLocalAlgCat Λ k} (f : Hom A B) (g : Hom B C) :
    (Hom.comp f g).hom =
      @AlgHom.comp Λ A.carrier B.carrier C.carrier _ _ _ _ A.algebra B.algebra C.algebra g.hom f.hom := sorry

/-- Morphisms are local `Λ`-algebra maps compatible with residue identifications. -/
theorem hom_spec {A B : ArtinianLocalAlgCat Λ k} (f : Hom A B) :
    IsLocalHom f.hom ∧ residueCompat f.hom f.isLocalHom = residueIsoHom A := sorry

/-- Composing an Artinian local algebra morphism with the identity of its source leaves it unchanged. -/
theorem Hom.id_comp {A B : ArtinianLocalAlgCat Λ k} (f : Hom A B) :
    Hom.comp (Hom.id A) f = f := sorry

/-- Composing an Artinian local algebra morphism with the identity of its target leaves it unchanged. -/
theorem Hom.comp_id {A B : ArtinianLocalAlgCat Λ k} (f : Hom A B) :
    Hom.comp f (Hom.id B) = f := sorry

/-- Composition of residue-compatible Artinian local algebra morphisms is associative. -/
theorem Hom.assoc {A B C D : ArtinianLocalAlgCat Λ k}
    (f : Hom A B) (g : Hom B C) (h : Hom C D) :
    Hom.comp (Hom.comp f g) h = Hom.comp f (Hom.comp g h) := sorry

/-- Category of Artinian local `Λ`-algebras with residue identification to `k`. -/
instance category : Category.{u} (ArtinianLocalAlgCat Λ k) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp f g
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

/-! Classical base rings and residue-field identifications. -/

/-- The classical case consists of a complete local base ring whose residue
field is identified with the chosen finite algebra `k`. -/
class IsClassical (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k]
    [Algebra Λ k] [Module.Finite Λ k] : Prop extends IsCompleteLocalRing Λ where
  /-- The structure map `Λ → k` is surjective. -/
  algebraMap_surjective : Function.Surjective (algebraMap Λ k)

/-- The residue field of a complete local ring is the canonical classical
choice for the residue field parameter. -/
instance instIsClassicalResidueField [IsCompleteLocalRing Λ] :
    IsClassical Λ (ResidueField Λ) where
  algebraMap_surjective := residue_surjective

/-- The classical condition is equivalent to completeness and surjectivity of
the structure map to `k`. -/
theorem isClassical_iff :
    IsClassical Λ k ↔ IsCompleteLocalRing Λ ∧ Function.Surjective (algebraMap Λ k) := sorry

/-- The classical condition canonically identifies the residue field of `Λ`
with `k`. -/
noncomputable def IsClassical.residueFieldIso [IsClassical Λ k] :
    ResidueField Λ ≃ₐ[Λ] k :=
  (Ideal.quotientEquivAlgOfEq Λ
      (ker_eq_maximalIdeal (Algebra.ofId Λ k : Λ →+* k) algebraMap_surjective).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (algebraMap_surjective : Function.Surjective (Algebra.ofId Λ k)))

/-- The canonical residue-field identification maps the residue of `x` to its
image under `algebraMap Λ k`. -/
theorem IsClassical.residueFieldIso_residue [IsClassical Λ k] (x : Λ) :
    IsClassical.residueFieldIso (residue Λ x) = algebraMap Λ k x := sorry

/-- An algebra equivalence from the residue field of a complete local ring to
`k` supplies the classical condition. -/
theorem ofResidueFieldIso [IsCompleteLocalRing Λ] (e : ResidueField Λ ≃ₐ[Λ] k) :
    IsClassical Λ k := sorry

end ArtinianLocalAlgCat
