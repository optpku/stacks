/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import stacks_project.Chap60.Remark_60_24_3_ech_complex_Cover
public import stacks_project.Chap60.Remark_60_24_3_ech_complex_Envelope
public import stacks_project.Chap60.Remark_60_24_3_ech_complex_Eval
public import stacks_project.Chap60.«60_17_0_1_Universal»
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Crystalline
open AlgebraicGeometry.Scheme.Modules
open CompletedCris
open CrystallineModuleSheaf
open CechCrisCover
open DividedPowers.PAdic

universe u

section EnvelopeData

variable (p : ℕ) [Fact (Nat.Prime p)]
variable {A : Type u} [CommRing A]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable (IA : Ideal A) (γA : DividedPowers IA)
variable {I : (Spec.{u} (.of A)).IdealSheafData}
variable {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
variable (c : CechCrisCover x₀)

/-- Envelope data on each simplex of a Čech crystalline covering. -/
structure CechCrisEnvelope where
  /-- Well-definedness of each simplex envelope. -/
  hIJ : ∀ n σ,
    Ideal.map (algebraMap A (c.simplexPolynomial n σ)) IA ≤ c.simplexKernel n σ
  /-- Chosen divided-power envelopes of the simplex kernels. -/
  E : ∀ n σ,
    DividedPowerEnvelope IA γA (algebraMap A (c.simplexPolynomial n σ))
      (c.simplexKernel n σ) (hIJ n σ)
  /-- Exponents witnessing that a power of `p` lies in the envelope ideal. -/
  N : ∀ (n : ℕ) (_ : Fin (n + 1) → c.Λ), ℕ
  /-- Membership of the chosen `p`-power in the envelope ideal. -/
  hN : ∀ n σ, Ideal.span {(p : (E n σ).D)} ^ N n σ ≤ (E n σ).D.ideal
  /-- Universality of each chosen simplex envelope. -/
  hE : ∀ n σ, DividedPowerEnvelope.IsUniversal γA
    (algebraMap A (c.simplexPolynomial n σ)) (hIJ n σ) (E n σ)

namespace CechCrisEnvelope

/-- Assemble simplex envelope data from well-defined universal envelopes. -/
def ofFamily
    (hIJ : ∀ n σ,
      Ideal.map (algebraMap A (c.simplexPolynomial n σ)) IA ≤ c.simplexKernel n σ)
    (E : ∀ n σ,
      DividedPowerEnvelope IA γA (algebraMap A (c.simplexPolynomial n σ))
        (c.simplexKernel n σ) (hIJ n σ))
    (N : ∀ (n : ℕ) (_ : Fin (n + 1) → c.Λ), ℕ)
    (hN : ∀ n σ, Ideal.span {(p : (E n σ).D)} ^ N n σ ≤ (E n σ).D.ideal)
    (hE : ∀ n σ, DividedPowerEnvelope.IsUniversal γA
      (algebraMap A (c.simplexPolynomial n σ)) (hIJ n σ) (E n σ)) :
    CechCrisEnvelope p IA γA c :=
  { hIJ, E, N, hN, hE }

end CechCrisEnvelope

end EnvelopeData

section EnvelopeMaps

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {A : Type u} [CommRing A]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {IA : Ideal A} {γA : DividedPowers IA}
variable {I : (Spec.{u} (.of A)).IdealSheafData}
variable {γS : ∀ V : (Spec.{u} (.of A)).affineOpens, DividedPowers (I.ideal V)}
variable {h_compatible :
    ∀ (V : (Spec.{u} (.of A)).affineOpens) (f : Γ(Spec (.of A), V)),
      (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen f))
        ((Spec (.of A)).presheaf.map
          (homOfLE ((Spec (.of A)).basicOpen_le f)).op).hom}
variable {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
variable {c : CechCrisCover x₀}

namespace CechCrisEnvelope

/-- Underlying function of a simplex operator. -/
def orderFun {n m : SimplexCategory} (f : n ⟶ m) :
    Fin (n.len + 1) → Fin (m.len + 1) :=
  SimplexCategory.Hom.toOrderHom f

/-- Reindexing of finite tuples along a simplex operator. -/
def reindex {n m : SimplexCategory} (f : n ⟶ m)
    (σ : Fin (m.len + 1) → c.Λ) : Fin (n.len + 1) → c.Λ :=
  fun i => σ (orderFun f i)

/-- Reindexing applies the order homomorphism of a simplex operator. -/
theorem reindex_apply {n m : SimplexCategory} (f : n ⟶ m)
    (σ : Fin (m.len + 1) → c.Λ) (i : Fin (n.len + 1)) :
    reindex f σ i = σ (SimplexCategory.Hom.toOrderHom f i) :=
  rfl

variable (E : CechCrisEnvelope p IA γA c)

/-- Canonical divided powers on the `p`-adic completion of a simplex envelope. -/
noncomputable def γhat (n : ℕ) (σ : Fin (n + 1) → c.Λ) :
    DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : (E.E n σ).D)})
        (E.E n σ).D.ideal (E.N n σ) (E.hN n σ))) :=
  envelopeCompletionDividedPowers (E.E n σ) (E.N n σ) (E.hN n σ)

/-- The completion map is a divided-power morphism for the canonical extension. -/
theorem hγhat (n : ℕ) (σ : Fin (n + 1) → c.Λ) :
    DividedPowers.IsDPMorphism (E.E n σ).D.dividedPowers (E.γhat n σ)
      (algebraMap (E.E n σ).D
        (AdicCompletion (Ideal.span {(p : (E.E n σ).D)}) (E.E n σ).D)) :=
  sorry

/-- The completed divided powers are the canonical ones. -/
theorem γhat_eq (n : ℕ) (σ : Fin (n + 1) → c.Λ) :
    E.γhat n σ = envelopeCompletionDividedPowers (E.E n σ) (E.N n σ) (E.hN n σ) :=
  rfl

/-- The polynomial comparison into a target envelope preserves divided powers on `IA`. -/
theorem simplexPolynomialMap_toEnvelope_isDPMorphism
    {n m : SimplexCategory} (f : n ⟶ m) (σ : Fin (m.len + 1) → c.Λ) :
    DividedPowers.IsDPMorphism γA (E.E m.len σ).D.dividedPowers
      (((E.E m.len σ).toD.comp
          (c.simplexPolynomialMap n.len m.len (orderFun f) σ).toRingHom).comp
        (algebraMap A (c.simplexPolynomial n.len (reindex f σ)))) :=
  sorry

/-- The polynomial comparison sends the source kernel into the target envelope ideal. -/
theorem simplexPolynomialMap_toEnvelope_ideal
    {n m : SimplexCategory} (f : n ⟶ m) (σ : Fin (m.len + 1) → c.Λ) :
    Ideal.map
      ((E.E m.len σ).toD.comp
        (c.simplexPolynomialMap n.len m.len (orderFun f) σ).toRingHom)
      (c.simplexKernel n.len (reindex f σ)) ≤
      (E.E m.len σ).D.ideal :=
  sorry

/-- Unique envelope lift `D_{σ ∘ f} ← P_{σ ∘ f}` through the target envelope. -/
noncomputable def envelopeLift {n m : SimplexCategory} (f : n ⟶ m)
    (σ : Fin (m.len + 1) → c.Λ) :
    (E.E n.len (reindex f σ)).D ⟶ (E.E m.len σ).D :=
  (E.hE n.len (reindex f σ)
      ((E.E m.len σ).toD.comp
        (c.simplexPolynomialMap n.len m.len (orderFun f) σ).toRingHom)
      (E.simplexPolynomialMap_toEnvelope_isDPMorphism f σ)
      (E.simplexPolynomialMap_toEnvelope_ideal f σ)).choose

/-- The envelope lift recovers the polynomial comparison on presentations. -/
theorem envelopeLift_spec {n m : SimplexCategory} (f : n ⟶ m)
    (σ : Fin (m.len + 1) → c.Λ) :
    (E.envelopeLift f σ).toRingHom.comp (E.E n.len (reindex f σ)).toD =
      (E.E m.len σ).toD.comp
        (c.simplexPolynomialMap n.len m.len (orderFun f) σ).toRingHom :=
  sorry

/-- Powers of `(p)` pull back along the envelope lift. -/
theorem envelopeLift_span_pow {n m : SimplexCategory} (f : n ⟶ m)
    (σ : Fin (m.len + 1) → c.Λ) (k : ℕ) :
    Ideal.span {(p : (E.E n.len (reindex f σ)).D)} ^ k ≤
      (Ideal.span {(p : (E.E m.len σ).D)} ^ k).comap
        (E.envelopeLift f σ).toRingHom :=
  sorry

/-- Stage maps of the completed envelope comparison. -/
noncomputable def homDStage {n m : SimplexCategory} (f : n ⟶ m)
    (σ : Fin (m.len + 1) → c.Λ) (k : ℕ) :
    AdicCompletion (Ideal.span {(p : (E.E n.len (reindex f σ)).D)})
      (E.E n.len (reindex f σ)).D →+*
      (E.E m.len σ).D ⧸ Ideal.span {(p : (E.E m.len σ).D)} ^ k :=
  (Ideal.quotientMap (Ideal.span {(p : (E.E m.len σ).D)} ^ k)
      (E.envelopeLift f σ).toRingHom (E.envelopeLift_span_pow f σ k)).comp
    (AdicCompletion.evalₐ (Ideal.span {(p : (E.E n.len (reindex f σ)).D)})
      k).toRingHom

/-- Compatibility of completed envelope stages with canonical factor maps. -/
theorem homDStage_compat {n m : SimplexCategory} (f : n ⟶ m)
    (σ : Fin (m.len + 1) → c.Λ) {a b : ℕ} (hle : a ≤ b) :
    (Ideal.Quotient.factorPow (Ideal.span {(p : (E.E m.len σ).D)}) hle).comp
        (E.homDStage f σ b) = E.homDStage f σ a :=
  sorry

/-- Functorial completed PD-envelope maps `D_{σ ∘ f} → D_σ`. -/
noncomputable def homD {n m : SimplexCategory} (f : n ⟶ m)
    (σ : Fin (m.len + 1) → c.Λ) :
    c.simplexEnvelope n.len (reindex f σ) (E.hIJ n.len (reindex f σ))
      (E.E n.len (reindex f σ)) (E.N n.len (reindex f σ))
      (E.hN n.len (reindex f σ)) (E.γhat n.len (reindex f σ)) →+*
      c.simplexEnvelope m.len σ (E.hIJ m.len σ) (E.E m.len σ) (E.N m.len σ)
        (E.hN m.len σ) (E.γhat m.len σ) :=
  AdicCompletion.liftRingHom (Ideal.span {(p : (E.E m.len σ).D)})
    (fun k => E.homDStage f σ k)
    (fun {_ _} hle => E.homDStage_compat f σ hle)

/-- The completed comparison lifts the polynomial presentation map through both envelopes. -/
theorem homD_spec {n m : SimplexCategory} (f : n ⟶ m)
    (σ : Fin (m.len + 1) → c.Λ) :
    (E.homD f σ).comp
        ((envelopeCompletionMap p A
            (c.simplexPolynomial n.len (reindex f σ)) IA γA
            (c.simplexKernel n.len (reindex f σ))
            (E.hIJ n.len (reindex f σ)) (E.E n.len (reindex f σ))
            (E.N n.len (reindex f σ)) (E.hN n.len (reindex f σ))
            (E.γhat n.len (reindex f σ))).comp
          (E.E n.len (reindex f σ)).toD) =
      (envelopeCompletionMap p A (c.simplexPolynomial m.len σ) IA γA
          (c.simplexKernel m.len σ) (E.hIJ m.len σ) (E.E m.len σ)
          (E.N m.len σ) (E.hN m.len σ) (E.γhat m.len σ)).comp
        ((E.E m.len σ).toD.comp
          (c.simplexPolynomialMap n.len m.len (orderFun f) σ).toRingHom) :=
  sorry

/-- Degreewise product ring `D(n) = ∏_σ D_σ`. -/
abbrev cechD (n : ℕ) : Type u :=
  ∀ σ : Fin (n + 1) → c.Λ,
    envelopeCompletionRing p A (c.simplexPolynomial n σ) IA γA
      (c.simplexKernel n σ) (E.hIJ n σ) (E.E n σ) (E.N n σ) (E.hN n σ) (E.γhat n σ)

/-- The degree-`n` ring is the product of simplex envelopes. -/
theorem cechD_obj (n : ℕ) :
    E.cechD n =
      ∀ σ : Fin (n + 1) → c.Λ,
        envelopeCompletionRing p A (c.simplexPolynomial n σ) IA γA
          (c.simplexKernel n σ) (E.hIJ n σ) (E.E n σ) (E.N n σ) (E.hN n σ)
          (E.γhat n σ) :=
  rfl

/-- Commutative ring structure on `D(n)`. -/
noncomputable instance cechD.commRing (n : ℕ) : CommRing (E.cechD n) :=
  inferInstance

/-- Product ring map `D(n) → D(m)` induced by envelope functoriality. -/
noncomputable def cechDHom {n m : SimplexCategory} (f : n ⟶ m) :
    E.cechD n.len →+* E.cechD m.len :=
  RingHom.pi fun σ =>
    (E.homD f σ).comp (Pi.evalRingHom _ (reindex f σ))

/-- Cosimplicial divided-power ring `D(*)`. -/
noncomputable def cechDCosimplicial : CosimplicialObject CommRingCat.{u} where
  obj n := CommRingCat.of (E.cechD n.len)
  map {_ _} f := CommRingCat.ofHom (E.cechDHom f)
  map_id := sorry
  map_comp := sorry

variable (s : Spec.{u} (.of A) ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
variable (hI : specIdealEqOfIdealTop IA I) (hγ : specDividedPowersEq IA γA I γS)
variable [HasLimits AddCommGrpCat.{u}]

/-- The completed envelope at a simplex, with its quotient to the chart. -/
abbrev completedSimplex (n : ℕ) (σ : Fin (n + 1) → c.Λ) :=
  c.simplexCrisObject n σ h_p (E.hIJ n σ) (E.E n σ) (E.hE n σ) (E.N n σ) (E.hN n σ)
    (E.γhat n σ) (E.hγhat n σ)

/-- The canonical completed envelope map preserves the canonical PD structures. -/
theorem homD_isDPMorphism {n m : SimplexCategory} (f : n ⟶ m)
    (σ : Fin (m.len + 1) → c.Λ) :
    DividedPowers.IsDPMorphism (E.completedSimplex h_p n.len (reindex f σ)).B.dividedPowers
      (E.completedSimplex h_p m.len σ).B.dividedPowers (E.homD f σ) := sorry

/-- The completed envelope comparison with its actual divided-power compatibility. -/
noncomputable def homDP {n m : SimplexCategory} (f : n ⟶ m)
    (σ : Fin (m.len + 1) → c.Λ) :
    DividedPowers.DPMorphism (E.completedSimplex h_p n.len (reindex f σ)).B.dividedPowers
      (E.completedSimplex h_p m.len σ).B.dividedPowers :=
  DividedPowers.DPMorphism.mk' (E.homD_isDPMorphism h_p f σ)

/-- The ring map on chart sections is restriction along the simplex inclusion. -/
def chartRestriction {n m : SimplexCategory} (f : n ⟶ m)
    (σ : Fin (m.len + 1) → c.Λ) :
    c.simplexRing n.len (reindex f σ) →+* c.simplexRing m.len σ :=
  (X.presheaf.map (homOfLE (c.simplexOpen_reindex_le (orderFun f) σ)).op).hom

/-- Completed envelope comparison commutes with the map from the base ring. -/
theorem homDP_base {n m : SimplexCategory} (f : n ⟶ m)
    (σ : Fin (m.len + 1) → c.Λ) :
    (E.homDP h_p f σ).toRingHom.comp
        (E.completedSimplex h_p n.len (reindex f σ)).base.toRingHom =
      (E.completedSimplex h_p m.len σ).base.toRingHom := sorry

/-- Completed envelope comparison induces the genuine restriction on closed fibres. -/
theorem homDP_quotient {n m : SimplexCategory} (f : n ⟶ m)
    (σ : Fin (m.len + 1) → c.Λ) :
    (E.completedSimplex h_p m.len σ).toC.comp (E.homDP h_p f σ).toRingHom =
      (chartRestriction f σ).comp (E.completedSimplex h_p n.len (reindex f σ)).toC := sorry

/-- The induced map of chart spectra commutes with their open immersions in `X`. -/
theorem chartRestriction_spec {n m : SimplexCategory} (f : n ⟶ m)
    (σ : Fin (m.len + 1) → c.Λ) :
    Spec.map (CommRingCat.ofHom (chartRestriction f σ)) ≫
        c.simplexSpecι n.len (reindex f σ) = c.simplexSpecι m.len σ := sorry

/-- Degreewise product module `M(n) = ∏_σ M_σ` of values of `F`. -/
abbrev cechM
    (F : CrisModuleSheaf (Spec (.of A)) I γS h_compatible X x₀) (n : ℕ) : Type u :=
  ∀ σ : Fin (n + 1) → c.Λ,
    c.simplexModule hI hγ F n σ s h_p (E.hIJ n σ) (E.E n σ) (E.hE n σ) (E.N n σ) (E.hN n σ)
      (E.γhat n σ) (E.hγhat n σ)

/-- The degree-`n` module is the product of simplex values of `F`. -/
theorem cechM_obj
    (F : CrisModuleSheaf (Spec (.of A)) I γS h_compatible X x₀) (n : ℕ) :
    E.cechM s h_p hI hγ F n =
      ∀ σ : Fin (n + 1) → c.Λ,
        c.simplexModule hI hγ F n σ s h_p (E.hIJ n σ) (E.E n σ) (E.hE n σ) (E.N n σ) (E.hN n σ)
          (E.γhat n σ) (E.hγhat n σ) :=
  rfl

/-- Additive group structure on `M(n)`. -/
noncomputable instance cechM.addCommGroup
    (F : CrisModuleSheaf (Spec (.of A)) I γS h_compatible X x₀) (n : ℕ) :
    AddCommGroup (E.cechM s h_p hI hγ F n) :=
  inferInstance

/-- Product module map `M(n) → M(m)` induced by envelope functoriality. -/
noncomputable def cechMHom
    (F : CrisModuleSheaf (Spec (.of A)) I γS h_compatible X x₀)
    {n m : SimplexCategory} (f : n ⟶ m) :
    E.cechM s h_p hI hγ F n.len →+ E.cechM s h_p hI hγ F m.len :=
  AddMonoidHom.pi fun σ =>
    (c.simplexModuleMap hI hγ F h_p
        (E.completedSimplex h_p n.len (reindex f σ)) (E.completedSimplex h_p m.len σ)
        (E.homDP h_p f σ) (chartRestriction f σ) (E.homDP_base h_p f σ)
        (E.homDP_quotient h_p f σ) (chartRestriction_spec f σ)).hom.comp
      (Pi.evalAddMonoidHom _ (reindex f σ))

/-- Cosimplicial abelian group `M(*)`. -/
noncomputable def cechMCosimplicial
    (F : CrisModuleSheaf (Spec (.of A)) I γS h_compatible X x₀) :
    CosimplicialObject AddCommGrpCat.{u} where
  obj n := AddCommGrpCat.of (E.cechM s h_p hI hγ F n.len)
  map {_ _} f := AddCommGrpCat.ofHom (E.cechMHom s h_p hI hγ F f)
  map_id := sorry
  map_comp := sorry

/-- Čech cochain complex `s(M(*))` associated to the cosimplicial module. -/
noncomputable def cechCrisComplex
    (F : CrisModuleSheaf (Spec (.of A)) I γS h_compatible X x₀) :
    CochainComplex AddCommGrpCat.{u} ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u}).obj
    (E.cechMCosimplicial s h_p hI hγ F)

/-- Degree-`n` cochains are isomorphic to the product module `M(n)`. -/
theorem cechCrisComplex_obj
    (F : CrisModuleSheaf (Spec (.of A)) I γS h_compatible X x₀) (n : ℕ) :
    IsIsomorphic ((E.cechCrisComplex s h_p hI hγ F).X n)
      (AddCommGrpCat.of (E.cechM s h_p hI hγ F n)) :=
  sorry


end CechCrisEnvelope

end EnvelopeMaps

end
