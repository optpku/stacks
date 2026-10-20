/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RingHom.PurelyInseparable
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.LocalRing.ResidueField.Compatible
public import ReasLib.RingTheory.RingHom.Local.Map

@[expose] public section

/-!
# Residue-compatible local algebra homomorphisms

Mathlib owns the canonical residue-field map induced by a local homomorphism,
and `AlgHom.Local` owns an explicit local algebra map.  This leaf supplies the
additional datum needed when a particular residue-field map is prescribed:
the commutative square with the two residue maps.  It does not choose a map
from an existence theorem and does not register any global instances.
-/

universe u v w x y

namespace AlgHom.Local

open IsLocalRing

section ResidueFieldMap

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommSemiring R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]
variable [IsLocalRing A] [IsLocalRing B]

/-- The canonical residue-field map induced by an explicit local algebra map.
The localness proof is carried by `f`, so users do not need to
install a noncanonical `IsLocalHom` instance merely to use Mathlib's map. -/
noncomputable def residueFieldMap
    (f : AlgHom.Local (R := R) (A := A) (B := B)) :
    ResidueField A →+* ResidueField B :=
  @ResidueField.map A B _ _ _ _ f.hom.toRingHom f.isLocal

/-- The canonical residue-field map of an explicit local algebra map commutes
with the two residue maps. -/
theorem residueFieldMap_comp_residue
    (f : AlgHom.Local (R := R) (A := A) (B := B)) :
    f.residueFieldMap.comp (residue A) =
      (residue B).comp f.hom.toRingHom := sorry

end ResidueFieldMap

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]
variable [IsLocalRing A] [IsLocalRing B]

/-- An explicit local `R`-algebra map together with a specified map of residue
fields compatible with the two residue maps. -/
structure ResidueCompatible (τ : ResidueField A →+* ResidueField B)
    extends toLocal : AlgHom.Local (R := R) (A := A) (B := B) where
  /-- The residue-field square associated to the local algebra map commutes. -/
  comm :
    (residue B).comp toLocal.hom.toRingHom =
      τ.comp (residue A)

/-- The explicit local algebra map underlying a residue-compatible map. -/
add_decl_doc ResidueCompatible.toLocal

namespace ResidueCompatible

/-- Build a residue-compatible local algebra map from an explicit local map
and its residue-field commutative square. -/
def of (f : AlgHom.Local (R := R) (A := A) (B := B))
    (τ : ResidueField A →+* ResidueField B)
    (comm :
      (residue B).comp f.hom.toRingHom =
        τ.comp (residue A)) :
    ResidueCompatible (R := R) (A := A) (B := B) τ :=
  { toLocal := f
    comm := comm }

/-- Residue-compatible local algebra maps are determined by their underlying
local algebra maps. -/
@[ext]
theorem ext
    {τ : ResidueField A →+* ResidueField B}
    {f g : ResidueCompatible (R := R) (A := A) (B := B) τ}
    (h : f.toLocal.hom = g.toLocal.hom) :
    f = g := sorry

/-- Transport a residue-compatible local algebra map when the prescribed
residue-field map is replaced by an equal map.  The transport is
confined to this API, so downstream statements need not expose dependent
casts. -/
def reindex
    {τ υ : ResidueField A →+* ResidueField B}
    (f : ResidueCompatible (R := R) (A := A) (B := B) τ)
    (h : τ = υ) :
    ResidueCompatible (R := R) (A := A) (B := B) υ :=
  h ▸ f

/-- Reindexing a prescribed residue-field map leaves the explicit local
algebra map unchanged. -/
@[simp]
theorem reindex_toLocal
    {τ υ : ResidueField A →+* ResidueField B}
    (f : ResidueCompatible (R := R) (A := A) (B := B) τ)
    (h : τ = υ) :
    (f.reindex h).toLocal = f.toLocal := sorry

/-- Reindexing a prescribed residue-field map leaves the underlying algebra
homomorphism unchanged. -/
@[simp]
theorem reindex_hom
    {τ υ : ResidueField A →+* ResidueField B}
    (f : ResidueCompatible (R := R) (A := A) (B := B) τ)
    (h : τ = υ) :
    (f.reindex h).toLocal.hom = f.toLocal.hom := sorry

/-- The prescribed residue-field map in a compatible square is the canonical
map induced by its explicit local algebra map. -/
theorem residueFieldMap_eq
    {τ : ResidueField A →+* ResidueField B}
    (f : ResidueCompatible (R := R) (A := A) (B := B) τ) :
    f.toLocal.residueFieldMap = τ := sorry

section Cospan

variable {R : Type u} {S : Type v} {A : Type w} {B : Type x}
variable [CommRing R] [CommRing S] [CommRing A] [CommRing B]
variable [Algebra R S] [Algebra R A] [Algebra S B] [Algebra R B]
variable [IsScalarTower R S B]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalRing A] [IsLocalRing B]
variable [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap R A)]
variable [IsLocalHom (algebraMap S B)]

/-- A residue-compatible local algebra map is compatible with the explicit
residue-field cospan determined by a scalar tower.  This forgets the algebra
presentation only after retaining the required base-map coherence. -/
theorem residueFieldCompatible
    {τ : ResidueField A →+* ResidueField B}
    (f : ResidueCompatible (R := R) (A := A) (B := B) τ) :
    IsLocalRing.ResidueField.Compatible
      (algebraMap R S) (algebraMap R A) (algebraMap S B) τ := sorry

end Cospan

/-- Bijectivity of the prescribed residue-field map is equivalent to
bijectivity of the canonical map induced by the explicit local algebra map. -/
theorem residueFieldMap_bijective_iff
    {τ : ResidueField A →+* ResidueField B}
    (f : ResidueCompatible (R := R) (A := A) (B := B) τ) :
    Function.Bijective f.toLocal.residueFieldMap ↔ Function.Bijective τ := sorry

/-- Pure inseparability of the prescribed residue-field map is equivalent to
pure inseparability of the canonical map induced by the explicit local algebra
map. -/
theorem residueFieldMap_isPurelyInseparable_iff
    {τ : ResidueField A →+* ResidueField B}
    (f : ResidueCompatible (R := R) (A := A) (B := B) τ) :
    f.toLocal.residueFieldMap.IsPurelyInseparable ↔ τ.IsPurelyInseparable := sorry

end ResidueCompatible

namespace ResidueCompatible

section RestrictScalars

variable {R : Type u} {S : Type v} {A : Type w} {B : Type x}
variable [CommRing R] [CommRing S] [CommRing A] [CommRing B]
variable [Algebra R S] [Algebra S A] [Algebra S B]
variable [Algebra R A] [Algebra R B]
variable [IsScalarTower R S A] [IsScalarTower R S B]
variable [IsLocalRing A] [IsLocalRing B]

/-- Restrict a residue-compatible local `S`-algebra map along a scalar tower.
The prescribed map of residue fields is unchanged, while the
underlying local algebra map is restricted explicitly. -/
def restrictScalars
    {τ : ResidueField A →+* ResidueField B}
    (f : ResidueCompatible (R := S) (A := A) (B := B) τ) :
    ResidueCompatible (R := R) (A := A) (B := B) τ where
  toLocal := f.toLocal.restrictScalars (R := R)
  comm := sorry

/-- Scalar restriction leaves the explicit local-map component of a
residue-compatible map equal to the corresponding scalar restriction. -/
@[simp]
theorem restrictScalars_toLocal
    {τ : ResidueField A →+* ResidueField B}
    (f : ResidueCompatible (R := S) (A := A) (B := B) τ) :
    (f.restrictScalars (R := R)).toLocal =
      f.toLocal.restrictScalars (R := R) := sorry

end RestrictScalars

section Composition

variable {R : Type u} {A : Type v} {B : Type w} {C : Type x}
variable [CommRing R] [CommRing A] [CommRing B] [CommRing C]
variable [Algebra R A] [Algebra R B] [Algebra R C]
variable [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]

/-- Compose residue-compatible local algebra maps over one fixed base.  Both
input residue-field maps are prescribed explicitly by the types
of `f` and `g`, and the output uses their displayed composite. -/
def comp
    {τ : ResidueField A →+* ResidueField B}
    {υ : ResidueField B →+* ResidueField C}
    (g : ResidueCompatible (R := R) (A := B) (B := C) υ)
    (f : ResidueCompatible (R := R) (A := A) (B := B) τ) :
    ResidueCompatible (R := R) (A := A) (B := C) (υ.comp τ) where
  toLocal := g.toLocal.comp f.toLocal
  comm := sorry

/-- The local-map component of a residue-compatible composite is the composite
of its explicit local-map components. -/
@[simp]
theorem comp_toLocal
    {τ : ResidueField A →+* ResidueField B}
    {υ : ResidueField B →+* ResidueField C}
    (g : ResidueCompatible (R := R) (A := B) (B := C) υ)
    (f : ResidueCompatible (R := R) (A := A) (B := B) τ) :
    (g.comp f).toLocal = g.toLocal.comp f.toLocal := sorry

end Composition

section RestrictScalarsComposition

variable {R : Type u} {S : Type v} {A : Type w} {B : Type x} {C : Type y}
variable [CommRing R] [CommRing S] [CommRing A] [CommRing B] [CommRing C]
variable [Algebra R S] [Algebra R A] [Algebra R B] [Algebra R C]
variable [Algebra S B] [Algebra S C]
variable [IsScalarTower R S B] [IsScalarTower R S C]
variable [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]

/-- Compose a residue-compatible local `R`-algebra map with a residue-compatible
local `S`-algebra map after restricting the latter along a
scalar tower.  No `S`-algebra structure on `A` is required. -/
def compRestrictScalars
    {τ : ResidueField A →+* ResidueField B}
    {υ : ResidueField B →+* ResidueField C}
    (g : ResidueCompatible (R := S) (A := B) (B := C) υ)
    (f : ResidueCompatible (R := R) (A := A) (B := B) τ) :
    ResidueCompatible (R := R) (A := A) (B := C) (υ.comp τ) :=
  (g.restrictScalars (R := R)).comp f

/-- The local-map component of scalar-restricted composition is the
corresponding composite of explicit local algebra maps. -/
@[simp]
theorem compRestrictScalars_toLocal
    {τ : ResidueField A →+* ResidueField B}
    {υ : ResidueField B →+* ResidueField C}
    (g : ResidueCompatible (R := S) (A := B) (B := C) υ)
    (f : ResidueCompatible (R := R) (A := A) (B := B) τ) :
    (g.compRestrictScalars f).toLocal =
      (g.toLocal.restrictScalars (R := R)).comp f.toLocal := sorry

/-- The algebra-homomorphism component of scalar-restricted composition is the
composite after restricting scalars. -/
@[simp]
theorem compRestrictScalars_hom
    {τ : ResidueField A →+* ResidueField B}
    {υ : ResidueField B →+* ResidueField C}
    (g : ResidueCompatible (R := S) (A := B) (B := C) υ)
    (f : ResidueCompatible (R := R) (A := A) (B := B) τ) :
    (g.compRestrictScalars f).toLocal.hom =
      (g.toLocal.hom.restrictScalars R).comp f.toLocal.hom := sorry

end RestrictScalarsComposition

end ResidueCompatible

end AlgHom.Local
