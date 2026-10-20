/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RationalFunction.GenericPoints
public import ReasLib.RingTheory.Localization.TotalQuotient.Product
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Rational functions on reduced Noetherian affine charts

Every component generic germ is sent through the canonical residue-field and fraction-ring
maps. The native finite-minimal-prime total-quotient equivalence combines these coordinates,
without assuming the chart is integral.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry nonZeroDivisors
noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.RationalFunction

variable (T : Scheme.{u}) [IsAffine T]

/-- The scheme point associated with an actual minimal prime of the affine section ring. -/
def componentPoint (q : minimalPrimes Γ(T, ⊤)) : T :=
  T.isoSpec.inv ⟨q.val, q.property.1.1⟩

set_option backward.isDefEq.respectTransparency false in
/-- The component point is an actual generic point. -/
theorem componentPoint_generic (q : minimalPrimes Γ(T, ⊤)) :
    componentPoint T q ∈ genericPoints T := by
  let p : PrimeSpectrum Γ(T, ⊤) := ⟨q.val, q.property.1.1⟩
  have hp : closure ({p} : Set (Spec (CommRingCat.of Γ(T, ⊤)))) ∈
      irreducibleComponents (Spec (CommRingCat.of Γ(T, ⊤))) := by
    apply PrimeSpectrum.vanishingIdeal_mem_minimalPrimes.mp
    rw [PrimeSpectrum.vanishingIdeal_singleton]
    exact q.property
  let e := T.isoSpec.inv.homeomorph
  have h := image_mem_irreducibleComponents_of_isPreirreducible_fiber e
    e.continuous e.isOpenMap
    (fun _ ↦ (Set.subsingleton_singleton.preimage e.injective).isPreirreducible)
    e.surjective hp
  rw [e.image_closure, Set.image_singleton] at h
  exact h

/-- The residue field at a component generic point maps canonically to the component fraction
field by the native Spec residue-field isomorphism. -/
def componentResidueMap (q : minimalPrimes Γ(T, ⊤)) :
    T.residueField (componentPoint T q) →+* FractionRing (Γ(T, ⊤) ⧸ q.val) :=
  (FractionRing.algEquiv (A := Γ(T, ⊤) ⧸ q.val) q.val.ResidueField).symm.toRingHom.comp
    ((Spec.residueFieldIso (CommRingCat.of Γ(T, ⊤)) ⟨q.val, q.property.1.1⟩).hom.hom.comp
      (T.isoSpec.inv.residueFieldMap ⟨q.val, q.property.1.1⟩).hom)

variable [IsLocallyNoetherian T]

local instance : IsNoetherianRing Γ(T, ⊤) :=
  IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top T⟩

local instance : NoetherianSpace T := noetherianSpace_of_isAffine

local instance : Finite (irreducibleComponents T) :=
  NoetherianSpace.finite_irreducibleComponents.to_subtype

/-- The actual component fractions of a rational function. -/
def componentFractions : Scheme.RationalFunction T →+*
    ∀ q : minimalPrimes Γ(T, ⊤), FractionRing (Γ(T, ⊤) ⧸ q.val) :=
  RingHom.pi fun q ↦ (componentResidueMap T q).comp
    ((Pi.evalRingHom (fun η : genericPoints T ↦ T.residueField η.val)
      ⟨componentPoint T q, componentPoint_generic T q⟩).comp
      T.rationalFunctionRingToPiResidueField)

/-- A dense-open representative computes by its germ at the corresponding component point. -/
theorem componentFractions_stage (U : DenseOpenIndex T) (s : sections T U)
    (q : minimalPrimes Γ(T, ⊤)) (hq : componentPoint T q ∈ U.val) :
    componentFractions T (stage T U s) q =
      componentResidueMap T q (T.residue (componentPoint T q)
        (T.presheaf.germ U.val (componentPoint T q) hq s)) := by
  change componentResidueMap T q
    (T.rationalFunctionRingToPiResidueField (stage T U s)
      ⟨componentPoint T q, componentPoint_generic T q⟩) = _
  rw [Scheme.rationalFunctionRingToPiResidueField_apply,
    Scheme.rationalFunctionRingToPiStalk_stage_apply T U s
      ⟨componentPoint T q, componentPoint_generic T q⟩ hq]

variable [AlgebraicGeometry.IsReduced T]

/-- The canonical total-quotient value assembled from all component fractions. -/
def toTotalQuotient : Scheme.RationalFunction T →+* FractionRing Γ(T, ⊤) :=
  (Localization.totalQuotientEquivFractionRingPi Γ(T, ⊤)
    (minimalPrimes.finite_of_isNoetherianRing Γ(T, ⊤))).symm.toRingHom.comp
      (componentFractions T)

/-- Computation of the assembled total-quotient value. -/
theorem toTotalQuotient_apply (a : Scheme.RationalFunction T) :
    toTotalQuotient T a =
      (Localization.totalQuotientEquivFractionRingPi Γ(T, ⊤)
        (minimalPrimes.finite_of_isNoetherianRing Γ(T, ⊤))).symm (componentFractions T a) := rfl

/-- The assembled value has exactly the supplied generic fraction in every component. -/
theorem toTotalQuotient_component (a : Scheme.RationalFunction T)
    (q : minimalPrimes Γ(T, ⊤)) :
    Localization.totalQuotientToFractionRingPi Γ(T, ⊤) (toTotalQuotient T a) q =
      componentFractions T a q := by
  exact congrFun ((Localization.totalQuotientEquivFractionRingPi Γ(T, ⊤)
    (minimalPrimes.finite_of_isNoetherianRing Γ(T, ⊤))).apply_symm_apply
      (componentFractions T a)) q


end AlgebraicGeometry.Scheme.RationalFunction
