module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import stacks_project.Chap60.Remark_60_24_3_ech_complex_Envelope
public import stacks_project.Chap60.Remark_60_24_3_ech_complex_Geometric
public import stacks_project.Chap60.Lemma_60_18_2
public import stacks_project.Chap60.Lemma_60_5_5

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Crystalline AlgebraicGeometry.Scheme.Modules
open CrystallineModuleSheaf DividedPowers.PAdic

universe u

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {A : Type u} [CommRing A]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]

/-- The ideal sheaf on `Spec A` is the quasi-coherent ideal associated to `IA`. -/
def specIdealEqOfIdealTop (IA : Ideal A) (I : (Spec.{u} (.of A)).IdealSheafData) : Prop :=
  I = Scheme.IdealSheafData.ofIdealTop
    (Ideal.comap (Scheme.ΓSpecIso (.of A)).hom.hom IA)

/-- Unfolding of `specIdealEqOfIdealTop` as equality of ideal sheaves. -/
theorem specIdealEqOfIdealTop_iff (IA : Ideal A)
    (I : (Spec.{u} (.of A)).IdealSheafData) :
    specIdealEqOfIdealTop IA I ↔
      I = Scheme.IdealSheafData.ofIdealTop
        (Ideal.comap (Scheme.ΓSpecIso (.of A)).hom.hom IA) :=
  sorry

/-- Global divided powers on `Spec A` recover `γA` along `ΓSpecIso`. -/
def specDividedPowersEq (IA : Ideal A) (γA : DividedPowers IA)
    (I : (Spec.{u} (.of A)).IdealSheafData)
    (γS : ∀ V : (Spec.{u} (.of A)).affineOpens, DividedPowers (I.ideal V)) : Prop :=
  DividedPowers.IsDPMorphism γA
    (γS ⟨⊤, isAffineOpen_top (Spec (.of A))⟩)
    (Scheme.ΓSpecIso (.of A)).inv.hom

/-- Unfolding of `specDividedPowersEq` as a divided-power morphism on global sections. -/
theorem specDividedPowersEq_iff (IA : Ideal A) (γA : DividedPowers IA)
    (I : (Spec.{u} (.of A)).IdealSheafData)
    (γS : ∀ V : (Spec.{u} (.of A)).affineOpens, DividedPowers (I.ideal V)) :
    specDividedPowersEq IA γA I γS ↔
      DividedPowers.IsDPMorphism γA
        (γS ⟨⊤, isAffineOpen_top (Spec (.of A))⟩)
        (Scheme.ΓSpecIso (.of A)).inv.hom :=
  sorry

/-- Source hypothesis of Proposition 60.21.1: comparisons `c_φ` are epimorphisms
whenever the thickening map is a closed immersion. -/
def comparison_epi_of_closedImmersion
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γS : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γS V).IsDPMorphism (γS (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (F : CrisModuleSheaf S I γS h_compatible X x₀) : Prop :=
  ∀ {T T' : smallCrystallineSite S I γS h_compatible X x₀} (φ : T ⟶ T'),
    IsClosedImmersion φ.hom.thickening → Epi (F.comparison φ)

/-- Hypothesis (2) applies to a closed immersion of thickenings. -/
theorem comparison_epi_of_closedImmersion_apply
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γS : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γS V).IsDPMorphism (γS (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    {F : CrisModuleSheaf S I γS h_compatible X x₀}
    (h : comparison_epi_of_closedImmersion S I γS h_compatible X x₀ F)
    {T T' : smallCrystallineSite S I γS h_compatible X x₀} (φ : T ⟶ T')
    (hφ : IsClosedImmersion φ.hom.thickening) :
    Epi (F.comparison φ) :=
  sorry

variable {IA : Ideal A} {γA : DividedPowers IA}
variable {I : (Spec.{u} (.of A)).IdealSheafData}
variable {γS : ∀ V : (Spec.{u} (.of A)).affineOpens, DividedPowers (I.ideal V)}
variable {h_compatible :
    ∀ (V : (Spec.{u} (.of A)).affineOpens) (f : Γ(Spec (.of A), V)),
      (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen f))
        ((Spec (.of A)).presheaf.map
          (homOfLE ((Spec (.of A)).basicOpen_le f)).op).hom}
variable {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}

namespace CechCrisCover

variable (c : CechCrisCover x₀)

/-- The open chart of a simplex intersection in `X`. -/
def simplexSpecι (n : ℕ) (σ : Fin (n + 1) → c.Λ) :
    Spec (.of (c.simplexRing n σ)) ⟶ X :=
  (c.isAffineIntersection n σ).isoSpec.inv ≫ (c.simplexOpen n σ).ι

/-- Each simplex chart is an open immersion. -/
theorem simplexSpecι_open (n : ℕ) (σ : Fin (n + 1) → c.Λ) :
    IsOpenImmersion (c.simplexSpecι n σ) := sorry

/-- The chart map uses the original `A`-algebra structure of its section ring. -/
theorem simplexSpecι_base (n : ℕ) (σ : Fin (n + 1) → c.Λ) :
    c.simplexSpecι n σ ≫ x₀ ≫ I.subschemeι =
      Spec.map (CommRingCat.ofHom (algebraMap A (c.simplexRing n σ))) := sorry

/-- The completed PD envelope of one simplex, with its real quotient to the chart. -/
def simplexCrisObject
    (n : ℕ) (σ : Fin (n + 1) → c.Λ)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (hIJ : Ideal.map (algebraMap A (c.simplexPolynomial n σ)) IA ≤ c.simplexKernel n σ)
    (E : DividedPowerEnvelope IA γA (algebraMap A (c.simplexPolynomial n σ))
      (c.simplexKernel n σ) hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γA
      (algebraMap A (c.simplexPolynomial n σ)) hIJ E)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN)))
    (hγhat : DividedPowers.IsDPMorphism E.D.dividedPowers γhat
      (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D))) :
    CompletedCrisObject p A IA γA (c.simplexRing n σ)
      (algebraMap A (c.simplexRing n σ)) (c.simplex_hIC IA n σ)
      (c.simplex_hpnil p h_p n σ) :=
  envelopeCompletedCrisObject p γA (algebraMap A (c.simplexRing n σ))
    (c.simplexSurjection n σ).toRingHom (c.simplexPolynomial_surjective n σ)
    (c.simplexSurjection n σ).comp_algebraMap
    (c.simplex_hIC IA n σ) (c.simplex_hpnil p h_p n σ) (c.simplexKernel_eq n σ)
    E hE N hN γhat hγhat

variable (hI : specIdealEqOfIdealTop IA I) (hγ : specDividedPowersEq IA γA I γS)
variable [HasLimits AddCommGrpCat.{u}]

/-- The value on a completed envelope is the inverse limit of `F` on its
genuine geometric PD thickenings. -/
def simplexModule
    (F : CrisModuleSheaf (Spec (.of A)) I γS h_compatible X x₀)
    (n : ℕ) (σ : Fin (n + 1) → c.Λ)
    (s : Spec.{u} (.of A) ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (hIJ : Ideal.map (algebraMap A (c.simplexPolynomial n σ)) IA ≤ c.simplexKernel n σ)
    (E : DividedPowerEnvelope IA γA (algebraMap A (c.simplexPolynomial n σ))
      (c.simplexKernel n σ) hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γA
      (algebraMap A (c.simplexPolynomial n σ)) hIJ E)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN)))
    (hγhat : DividedPowers.IsDPMorphism E.D.dividedPowers γhat
      (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D))) : AddCommGrpCat.{u} :=
  completedSections γA (c.simplex_hIC IA n σ) (c.simplex_hpnil p h_p n σ)
    I γS h_compatible x₀ (c.simplexSpecι n σ) (c.simplexSpecι_base n σ) hI hγ
    (c.simplexSpecι_open n σ) (c.simplexCrisObject n σ h_p hIJ E hE N hN γhat hγhat)
    (toAbelianPresheaf (Spec (.of A)) I γS h_compatible X x₀ F)

/-- The comparison on values of completed envelopes is induced by a PD map
compatible with the base and the open charts. -/
def simplexModuleMap
    (F : CrisModuleSheaf (Spec (.of A)) I γS h_compatible X x₀)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    {n m : ℕ} {τ : Fin (n + 1) → c.Λ} {σ : Fin (m + 1) → c.Λ}
    (Z : CompletedCrisObject p A IA γA (c.simplexRing n τ)
      (algebraMap A (c.simplexRing n τ)) (c.simplex_hIC IA n τ) (c.simplex_hpnil p h_p n τ))
    (W : CompletedCrisObject p A IA γA (c.simplexRing m σ)
      (algebraMap A (c.simplexRing m σ)) (c.simplex_hIC IA m σ) (c.simplex_hpnil p h_p m σ))
    (φ : DividedPowers.DPMorphism Z.B.dividedPowers W.B.dividedPowers)
    (g : c.simplexRing n τ →+* c.simplexRing m σ)
    (hbase : φ.toRingHom.comp Z.base.toRingHom = W.base.toRingHom)
    (hquot : W.toC.comp φ.toRingHom = g.comp Z.toC)
    (hchart : Spec.map (CommRingCat.ofHom g) ≫ c.simplexSpecι n τ = c.simplexSpecι m σ) :
    completedSections γA (c.simplex_hIC IA n τ) (c.simplex_hpnil p h_p n τ)
        I γS h_compatible x₀ (c.simplexSpecι n τ) (c.simplexSpecι_base n τ)
        hI hγ (c.simplexSpecι_open n τ) Z
        (toAbelianPresheaf (Spec (.of A)) I γS h_compatible X x₀ F) ⟶
      completedSections γA (c.simplex_hIC IA m σ) (c.simplex_hpnil p h_p m σ)
        I γS h_compatible x₀ (c.simplexSpecι m σ) (c.simplexSpecι_base m σ)
        hI hγ (c.simplexSpecι_open m σ) W
        (toAbelianPresheaf (Spec (.of A)) I γS h_compatible X x₀ F) :=
  crossCompletedSectionsMap γA (c.simplex_hIC IA n τ) (c.simplex_hpnil p h_p n τ)
    I γS h_compatible x₀ (c.simplexSpecι n τ) (c.simplexSpecι_base n τ)
    hI hγ (c.simplexSpecι_open n τ) Z
    (c.simplex_hIC IA m σ) (c.simplex_hpnil p h_p m σ) W φ
    (c.simplexSpecι m σ) (c.simplexSpecι_base m σ) (c.simplexSpecι_open m σ)
    g hbase hquot hchart (toAbelianPresheaf (Spec (.of A)) I γS h_compatible X x₀ F)

end CechCrisCover

end
