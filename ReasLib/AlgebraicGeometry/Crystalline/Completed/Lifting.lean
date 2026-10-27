/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Smooth.StrongLifting
public import ReasLib.AlgebraicGeometry.Crystalline.Completed.EnvelopeConnection
public import ReasLib.RingTheory.Kaehler.DeRham.Connection.Adic.BaseChange
public import Mathlib.CategoryTheory.Equivalence

@[expose] public section

noncomputable section

set_option backward.privateInPublic true
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory DPPolynomial.DeRham
open AlgebraicGeometry.Scheme.Crystalline
open scoped TensorProduct

universe u

namespace CrystallineModuleSheaf.CrisModuleSheaf.Completed.Lifting

variable (p : ℕ) [Fact p.Prime]
variable {A C P : Type u} [CommRing A] [CommRing C] [CommRing P]
variable [Algebra A C] [Algebra A P]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {I : Ideal A} (γ : DividedPowers I)
variable (π : P →ₐ[A] C) (hπ : Function.Surjective π)
variable {J : Ideal P} (hJ : J = RingHom.ker π.toRingHom)
variable (hIC : Ideal.map (algebraMap A C) I = ⊥) (hpnil : IsNilpotent (p : C))
variable {hIJ : Ideal.map (algebraMap A P) I ≤ J}
variable (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
variable (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A P) hIJ E)

/-- Completed pullback of a connection to a specified compatible polynomial envelope. -/
def polynomialConnection (M : ModuleCat.{u} (Envelope.ring p E))
    (conn : Envelope.connectionType p E M)
    {ι : Type u} (π₀ : MvPolynomial ι A →ₐ[A] C) (hπ₀ : Function.Surjective π₀)
    {J₀ : Ideal (MvPolynomial ι A)} (hJ₀ : J₀ = RingHom.ker π₀.toRingHom)
    {hIJ₀ : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ J₀}
    (E₀ : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) J₀ hIJ₀)
    (hE₀ : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial ι A)) hIJ₀ E₀)
    (φ : Envelope.ring p E →+* Envelope.ring p E₀)
    (hbase : φ.comp (Envelope.envelopeObject p γ π hπ hJ hIC hpnil E hE).base.toRingHom =
      (Envelope.envelopeObject p γ π₀ hπ₀ hJ₀ hIC hpnil E₀ hE₀).base.toRingHom)
    (hDP : (Envelope.completionPowers p γ π hπ hJ hIC hpnil E hE).IsDPMorphism
      (Envelope.completionPowers p γ π₀ hπ₀ hJ₀ hIC hpnil E₀ hE₀) φ) : Envelope.connectionType p E₀
      (Connection.Adic.completedScalarExtension φ p M) :=
  Connection.Adic.baseChange
    (E.toD.comp (algebraMap A P)) (E₀.toD.comp (algebraMap A (MvPolynomial ι A)))
    E.D.dividedPowers E₀.D.dividedPowers p
    (Envelope.quotientNilpotent p γ π hπ hJ hIC hpnil E hE) (Envelope.quotientNilpotent p γ π₀ hπ₀ hJ₀ hIC hpnil E₀ hE₀)
    (Envelope.completionPowers p γ π hπ hJ hIC hpnil E hE) (Envelope.completionPowers p γ π₀ hπ₀ hJ₀ hIC hpnil E₀ hE₀)
    (Envelope.completionPowers_extends p γ π hπ hJ hIC hpnil E hE) (Envelope.completionPowers_extends p γ π₀ hπ₀ hJ₀ hIC hpnil E₀ hE₀)
    φ ((congrArg φ.comp (Envelope.baseMap_eq p γ π hπ hJ hIC hpnil E hE)).symm.trans
      (hbase.trans (Envelope.baseMap_eq p γ π₀ hπ₀ hJ₀ hIC hpnil E₀ hE₀))) hDP M conn

/-- A connection is quasi-nilpotent if every compatible polynomial-envelope pullback is coordinatewise topologically quasi-nilpotent. -/
def IsQuasiNilpotent (M : ModuleCat.{u} (Envelope.ring p E))
    (conn : Envelope.connectionType p E M) : Prop :=
  ∀ {ι : Type u} (π₀ : MvPolynomial ι A →ₐ[A] C) (hπ₀ : Function.Surjective π₀)
    {J₀ : Ideal (MvPolynomial ι A)} (hJ₀ : J₀ = RingHom.ker π₀.toRingHom)
    {hIJ₀ : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ J₀}
    (E₀ : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) J₀ hIJ₀)
    (hE₀ : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial ι A)) hIJ₀ E₀),
    ∀ (φ : Envelope.ring p E →+* Envelope.ring p E₀)
    (hbase : φ.comp (Envelope.envelopeObject p γ π hπ hJ hIC hpnil E hE).base.toRingHom =
      (Envelope.envelopeObject p γ π₀ hπ₀ hJ₀ hIC hpnil E₀ hE₀).base.toRingHom)
    (hDP : (Envelope.completionPowers p γ π hπ hJ hIC hpnil E hE).IsDPMorphism
      (Envelope.completionPowers p γ π₀ hπ₀ hJ₀ hIC hpnil E₀ hE₀) φ), ∀ (hquot : (Envelope.envelopeObject p γ π₀ hπ₀ hJ₀ hIC hpnil E₀ hE₀).toC.comp φ =
      (Envelope.envelopeObject p γ π hπ hJ hIC hpnil E hE).toC),
      -- Local instance justification (noncanonical choice): polynomial coordinates use the structural map of this test envelope.
      letI := DividedPowerEnvelope.Coordinates.baseAlgebra E₀
      Connection.Adic.IsTopologicallyQuasiNilpotent
      (polynomialConnection p γ π hπ hJ hIC hpnil E hE M conn π₀ hπ₀ hJ₀ E₀ hE₀ φ hbase hDP)
      (AdicCompletion.isAdicComplete (Submodule.fg_span_singleton (p : Envelope.ring p E₀)))
      (DividedPowerEnvelope.Coordinates.completedCoord E₀ hE₀ p)

/-- Universal quasi-nilpotence implies quasi-nilpotence on each specified compatible polynomial test. -/
theorem isQuasiNilpotent_test (M : ModuleCat.{u} (Envelope.ring p E))
    (conn : Envelope.connectionType p E M) (hqn : IsQuasiNilpotent p γ π hπ hJ hIC hpnil E hE M conn)
    {ι : Type u} (π₀ : MvPolynomial ι A →ₐ[A] C) (hπ₀ : Function.Surjective π₀)
    {J₀ : Ideal (MvPolynomial ι A)} (hJ₀ : J₀ = RingHom.ker π₀.toRingHom)
    {hIJ₀ : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ J₀}
    (E₀ : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) J₀ hIJ₀)
    (hE₀ : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial ι A)) hIJ₀ E₀)
    (φ : Envelope.ring p E →+* Envelope.ring p E₀)
    (hbase : φ.comp (Envelope.envelopeObject p γ π hπ hJ hIC hpnil E hE).base.toRingHom =
      (Envelope.envelopeObject p γ π₀ hπ₀ hJ₀ hIC hpnil E₀ hE₀).base.toRingHom)
    (hDP : (Envelope.completionPowers p γ π hπ hJ hIC hpnil E hE).IsDPMorphism
      (Envelope.completionPowers p γ π₀ hπ₀ hJ₀ hIC hpnil E₀ hE₀) φ) (hquot : (Envelope.envelopeObject p γ π₀ hπ₀ hJ₀ hIC hpnil E₀ hE₀).toC.comp φ =
      (Envelope.envelopeObject p γ π hπ hJ hIC hpnil E hE).toC) :
    -- Local instance justification (noncanonical choice): polynomial coordinates use the structural map of this test envelope.
    letI := DividedPowerEnvelope.Coordinates.baseAlgebra E₀
    Connection.Adic.IsTopologicallyQuasiNilpotent
      (polynomialConnection p γ π hπ hJ hIC hpnil E hE M conn π₀ hπ₀ hJ₀ E₀ hE₀ φ hbase hDP)
      (AdicCompletion.isAdicComplete (Submodule.fg_span_singleton (p : Envelope.ring p E₀)))
      (DividedPowerEnvelope.Coordinates.completedCoord E₀ hE₀ p) := sorry

/-- Strong lifting guarantees a compatible polynomial presentation and completed divided-power comparison. -/
theorem polynomialTest_exists [Algebra.HasStrongLifting A P] :
    ∃ (ι : Type u) (π₀ : MvPolynomial ι A →ₐ[A] C) (hπ₀ : Function.Surjective π₀)
      (J₀ : Ideal (MvPolynomial ι A)) (hJ₀ : J₀ = RingHom.ker π₀.toRingHom)
      (hIJ₀ : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ J₀)
      (E₀ : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) J₀ hIJ₀)
      (hE₀ : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial ι A)) hIJ₀ E₀)
      (φ : Envelope.ring p E →+* Envelope.ring p E₀),
      φ.comp (Envelope.envelopeObject p γ π hπ hJ hIC hpnil E hE).base.toRingHom =
          (Envelope.envelopeObject p γ π₀ hπ₀ hJ₀ hIC hpnil E₀ hE₀).base.toRingHom ∧
      (Envelope.completionPowers p γ π hπ hJ hIC hpnil E hE).IsDPMorphism
          (Envelope.completionPowers p γ π₀ hπ₀ hJ₀ hIC hpnil E₀ hE₀) φ ∧
      (Envelope.envelopeObject p γ π₀ hπ₀ hJ₀ hIC hpnil E₀ hE₀).toC.comp φ =
          (Envelope.envelopeObject p γ π hπ hJ hIC hpnil E hE).toC := sorry

/-- Complete intrinsically integrable connections satisfying all compatible polynomial tests, with horizontal morphisms. -/
def pairCategory : Cat :=
  -- Local instance justification (noncanonical choice): relative forms use the structural map of this explicit envelope.
  letI := (E.toD.comp (algebraMap A P)).toAlgebra
  ⟨(Σ M : ModuleCat.{u} (Envelope.ring p E),
      {conn : Envelope.connectionType p E M //
        IsAdicComplete (Ideal.span {(p : Envelope.ring p E)}) M ∧
        Connection.Adic.IsIntegrable A E.D E.D.dividedPowers p conn ∧
        IsQuasiNilpotent p γ π hπ hJ hIC hpnil E hE M conn}),
    { Hom := fun M N ↦ Connection.Adic.Hom M.2.val N.2.val
      id := fun M ↦ Connection.Adic.Hom.id M.2.val
      comp := fun f g ↦ Connection.Adic.Hom.comp f g
      id_comp := Connection.Adic.Hom.id_comp
      comp_id := Connection.Adic.Hom.comp_id
      assoc := Connection.Adic.Hom.assoc }⟩

/-- Construct a connection object from its coefficients, connection, completeness, curvature, and universal test laws. -/
def pairOf (M : ModuleCat.{u} (Envelope.ring p E)) (conn : Envelope.connectionType p E M)
    (hcomplete : IsAdicComplete (Ideal.span {(p : Envelope.ring p E)}) M)
    (hintegrable :
      -- Local instance justification (noncanonical choice): relative forms use the structural map of this explicit envelope.
      letI := (E.toD.comp (algebraMap A P)).toAlgebra
      Connection.Adic.IsIntegrable A E.D E.D.dividedPowers p conn)
    (hqn : IsQuasiNilpotent p γ π hπ hJ hIC hpnil E hE M conn) : pairCategory p γ π hπ hJ hIC hpnil E hE :=
  ⟨M, conn, hcomplete, hintegrable, hqn⟩

/-- Connection objects have complete coefficients, the completed Leibniz law, zero curvature, and universal polynomial quasi-nilpotence. -/
theorem pairCategory_spec (V : pairCategory p γ π hπ hJ hIC hpnil E hE) :
    -- Local instance justification (noncanonical choice): relative forms use the structural map of this explicit envelope.
    letI := (E.toD.comp (algebraMap A P)).toAlgebra
    IsAdicComplete (Ideal.span {(p : Envelope.ring p E)}) V.1 ∧
    (∀ (r : Envelope.ring p E) (m : V.1), V.2.val.toAddMonoidHom (r • m) =
      r • V.2.val.toAddMonoidHom m +
        AdicCompletion.of (Ideal.span {(p : Envelope.ring p E)}) _
          (m ⊗ₜ[Envelope.ring p E] completedDerivation A E.D E.D.dividedPowers p r)) ∧
    Connection.Adic.IsIntegrable A E.D E.D.dividedPowers p V.2.val ∧
    IsQuasiNilpotent p γ π hπ hJ hIC hpnil E hE V.1 V.2.val := sorry

variable {X : Scheme.{u}} (IS : (Spec (.of A)).IdealSheafData)
variable (γS : ∀ V : (Spec (.of A)).affineOpens, DividedPowers (IS.ideal V))
variable (hc : ∀ (V : (Spec (.of A)).affineOpens) (a : Γ(Spec (.of A), V)),
  (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen a))
    ((Spec (.of A)).presheaf.map (homOfLE ((Spec (.of A)).basicOpen_le a)).op).hom)
variable (x₀ : X ⟶ IS.subscheme) (eX : Spec (.of C) ≅ X)
variable (heX : eX.hom ≫ x₀ ≫ IS.subschemeι = Spec.map (CommRingCat.ofHom (algebraMap A C)))
variable (hI : IS = DividedPowers.affineIdeal (I := I))
variable (hγ : DividedPowers.IsDPMorphism γ
  (γS ⟨⊤, isAffineOpen_top (Spec (.of A))⟩) (Scheme.ΓSpecIso (.of A)).inv.hom)
variable (F : CrisModuleSheaf (Spec (.of A)) IS γS hc X x₀)

variable [IsCrystal F] [IsLocallyQuasiCoherent F]

/-- Crystalline pullback to every compatible polynomial envelope gives a topologically quasi-nilpotent connection. -/
theorem connection_isQuasiNilpotent :
    IsQuasiNilpotent p γ π hπ hJ hIC hpnil E hE (Envelope.coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F)
      (Envelope.connection p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) := sorry

/-- Quasi-coherent crystals are crystalline modules with the crystal and local quasi-coherence properties. -/
abbrev quasiCoherentCrystals :=
  ObjectProperty.FullSubcategory (fun F : CrisModuleSheaf (Spec (.of A)) IS γS hc X x₀ ↦
    IsCrystal F ∧ IsLocallyQuasiCoherent F)

/-- The connection object of a crystal uses its actual inverse-limit coefficients and canonical differential. -/
private def crystalPair (F : quasiCoherentCrystals IS γS hc x₀) : pairCategory p γ π hπ hJ hIC hpnil E hE :=
  -- Local instance justification (proof-local temporary data): the full-subcategory predicate supplies the crystal law for this evaluation.
  letI : IsCrystal F.obj := F.property.1
  -- Local instance justification (proof-local temporary data): the full-subcategory predicate supplies quasi-coherence for this evaluation.
  letI : IsLocallyQuasiCoherent F.obj := F.property.2
  pairOf p γ π hπ hJ hIC hpnil E hE (Envelope.coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F.obj)
    (Envelope.connection p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F.obj)
    (Envelope.coefficientModule_isAdicComplete p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F.obj)
    (Envelope.connection_isIntegrable p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F.obj)
    (connection_isQuasiNilpotent p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F.obj)

/-- Quasi-coherent crystals map to their canonical complete integrable universally quasi-nilpotent envelope connections. -/
def toConnectionPairs :
    quasiCoherentCrystals IS γS hc x₀ ⥤ pairCategory p γ π hπ hJ hIC hpnil E hE where
  obj F := crystalPair p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F
  map {F G} φ :=
    -- Local instance justification (proof-local temporary data): the bundled crystal F supplies its own crystal law.
    letI : IsCrystal F.obj := F.property.1
    -- Local instance justification (proof-local temporary data): the bundled crystal F supplies its own local quasi-coherence law.
    letI : IsLocallyQuasiCoherent F.obj := F.property.2
    -- Local instance justification (proof-local temporary data): the bundled crystal G supplies its own crystal law.
    letI : IsCrystal G.obj := G.property.1
    -- Local instance justification (proof-local temporary data): the bundled crystal G supplies its own local quasi-coherence law.
    letI : IsLocallyQuasiCoherent G.obj := G.property.2
    Envelope.connectionMap p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F.obj φ.hom
  map_id F :=
    -- Local instance justification (proof-local temporary data): the bundled crystal F supplies its own crystal law.
    letI : IsCrystal F.obj := F.property.1
    -- Local instance justification (proof-local temporary data): the bundled crystal F supplies its own local quasi-coherence law.
    letI : IsLocallyQuasiCoherent F.obj := F.property.2
    Envelope.connectionMap_id p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F.obj
  map_comp {F G H} φ ψ :=
    -- Local instance justification (proof-local temporary data): the bundled crystal F supplies its own crystal law.
    letI : IsCrystal F.obj := F.property.1
    -- Local instance justification (proof-local temporary data): the bundled crystal F supplies its own local quasi-coherence law.
    letI : IsLocallyQuasiCoherent F.obj := F.property.2
    -- Local instance justification (proof-local temporary data): the bundled crystal G supplies its own crystal law.
    letI : IsCrystal G.obj := G.property.1
    -- Local instance justification (proof-local temporary data): the bundled crystal G supplies its own local quasi-coherence law.
    letI : IsLocallyQuasiCoherent G.obj := G.property.2
    -- Local instance justification (proof-local temporary data): the bundled crystal H supplies its own crystal law.
    letI : IsCrystal H.obj := H.property.1
    -- Local instance justification (proof-local temporary data): the bundled crystal H supplies its own local quasi-coherence law.
    letI : IsLocallyQuasiCoherent H.obj := H.property.2
    Envelope.connectionMap_comp p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F.obj φ.hom ψ.hom

/-- The functor returns precisely the inverse-limit coefficient module and its canonical completed connection. -/
theorem toConnectionPairs_obj_spec
    (F : quasiCoherentCrystals IS γS hc x₀) :
    -- Local instance justification (proof-local temporary data): the object carries its crystal law in the full-subcategory predicate.
    letI : IsCrystal F.obj := F.property.1
    -- Local instance justification (proof-local temporary data): the object carries quasi-coherence in the full-subcategory predicate.
    letI : IsLocallyQuasiCoherent F.obj := F.property.2
    ((toConnectionPairs p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ).obj F).1 = Envelope.coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F.obj ∧
      ((toConnectionPairs p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ).obj F).2.val = Envelope.connection p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F.obj := sorry

/-- Strong lifting makes the canonical crystalline connection functor faithful. -/
instance toConnectionPairs_faithful [Algebra.HasStrongLifting A P] :
    (toConnectionPairs p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ).Faithful := sorry

/-- Horizontal maps for universally quasi-nilpotent connections descend uniquely to crystalline module morphisms. -/
instance toConnectionPairs_full [Algebra.HasStrongLifting A P] :
    (toConnectionPairs p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ).Full := sorry

/-- Every complete integrable universally quasi-nilpotent envelope connection comes from a quasi-coherent crystal. -/
instance toConnectionPairs_essSurj [Algebra.HasStrongLifting A P] :
    (toConnectionPairs p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ).EssSurj := sorry

/-- A strong-lifting algebra presentation identifies quasi-coherent crystals with complete integrable universally quasi-nilpotent envelope connections. -/
instance toConnectionPairs_isEquivalence [Algebra.HasStrongLifting A P] :
    (toConnectionPairs p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ).IsEquivalence :=
  { faithful := toConnectionPairs_faithful p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ
    full := toConnectionPairs_full p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ
    essSurj := toConnectionPairs_essSurj p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ }

end CrystallineModuleSheaf.CrisModuleSheaf.Completed.Lifting
