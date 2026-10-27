/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Cech.Envelope
public import ReasLib.AlgebraicGeometry.Crystalline.Completed.Geometry
public import ReasLib.AlgebraicGeometry.Crystalline.Affine
public import ReasLib.RingTheory.DividedPowers.Envelope.Crystalline

@[expose] public section

noncomputable section


open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Crystalline AlgebraicGeometry.Scheme.Modules
open CrystallineModuleSheaf DividedPowers.PAdic

universe u

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

namespace CechCrisCover

variable (c : CechCrisCover x₀)

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
      (algebraMap A (c.simplexRing n σ))
      (Affine.ideal_map_eq_bot_of_map_le_ker IA (c.simplexSurjection n σ) hIJ)
      (c.simplex_hpnil p h_p n σ) :=
  envelopeCompletedCrisObject p γA (algebraMap A (c.simplexRing n σ))
    (c.simplexSurjection n σ).toRingHom (c.simplexPolynomial_surjective n σ)
    (c.simplexSurjection n σ).comp_algebraMap
    (Affine.ideal_map_eq_bot_of_map_le_ker IA (c.simplexSurjection n σ) hIJ)
    (c.simplex_hpnil p h_p n σ) (c.simplexKernel_eq n σ)
    E hE N hN γhat hγhat

variable (hI : Affine.idealCompatible IA I) (hγ : Affine.dividedPowersCompatible IA γA I γS)
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
  completedSections (C := c.simplexRing n σ) γA (c.simplex_hIC IA hI n σ) (c.simplex_hpnil p h_p n σ)
    I γS h_compatible x₀ (c.simplexSpecι n σ) (c.simplexSpecι_base n σ) hI hγ
    (c.simplexSpecι_open n σ) (c.simplexCrisObject n σ h_p hIJ E hE N hN γhat hγhat)
    (toAbelianPresheaf (Spec (.of A)) I γS h_compatible X x₀ F)

/-- The completed simplex ring acts on its inverse-limit coefficient sections. -/
abbrev simplexModuleStructure
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
      (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D))) :
    Module
      (envelopeCompletionRing p A (c.simplexPolynomial n σ) IA γA
        (c.simplexKernel n σ) hIJ E N hN γhat)
      (c.simplexModule hI hγ F n σ s h_p hIJ E hE N hN γhat hγhat) :=
  completedSectionsModule (C := c.simplexRing n σ) γA (c.simplex_hIC IA hI n σ) (c.simplex_hpnil p h_p n σ)
    I γS h_compatible x₀ (c.simplexSpecι n σ) (c.simplexSpecι_base n σ) hI hγ
    (c.simplexSpecι_open n σ) (c.simplexCrisObject n σ h_p hIJ E hE N hN γhat hγhat)
    F

/-- The comparison on values of completed envelopes is induced by a PD map
compatible with the base and the open charts. -/
def simplexModuleMap
    (F : CrisModuleSheaf (Spec (.of A)) I γS h_compatible X x₀)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    {n m : ℕ} {τ : Fin (n + 1) → c.Λ} {σ : Fin (m + 1) → c.Λ}
    (Z : CompletedCrisObject p A IA γA (c.simplexRing n τ)
      (algebraMap A (c.simplexRing n τ)) (c.simplex_hIC IA hI n τ) (c.simplex_hpnil p h_p n τ))
    (W : CompletedCrisObject p A IA γA (c.simplexRing m σ)
      (algebraMap A (c.simplexRing m σ)) (c.simplex_hIC IA hI m σ) (c.simplex_hpnil p h_p m σ))
    (φ : DividedPowers.DPMorphism Z.B.dividedPowers W.B.dividedPowers)
    (g : c.simplexRing n τ →+* c.simplexRing m σ)
    (hbase : φ.toRingHom.comp Z.base.toRingHom = W.base.toRingHom)
    (hquot : W.toC.comp φ.toRingHom = g.comp Z.toC)
    (hchart : Spec.map (CommRingCat.ofHom g) ≫ c.simplexSpecι n τ = c.simplexSpecι m σ) :
    completedSections (C := c.simplexRing n τ) γA (c.simplex_hIC IA hI n τ) (c.simplex_hpnil p h_p n τ)
        I γS h_compatible x₀ (c.simplexSpecι n τ) (c.simplexSpecι_base n τ)
        hI hγ (c.simplexSpecι_open n τ) Z
        (toAbelianPresheaf (Spec (.of A)) I γS h_compatible X x₀ F) ⟶
      completedSections (C := c.simplexRing m σ) γA (c.simplex_hIC IA hI m σ) (c.simplex_hpnil p h_p m σ)
        I γS h_compatible x₀ (c.simplexSpecι m σ) (c.simplexSpecι_base m σ)
        hI hγ (c.simplexSpecι_open m σ) W
        (toAbelianPresheaf (Spec (.of A)) I γS h_compatible X x₀ F) :=
  crossCompletedSectionsMap (C := c.simplexRing n τ) (C' := c.simplexRing m σ)
    γA (c.simplex_hIC IA hI n τ) (c.simplex_hpnil p h_p n τ)
    I γS h_compatible x₀ (c.simplexSpecι n τ) (c.simplexSpecι_base n τ)
    hI hγ (c.simplexSpecι_open n τ) Z
    (c.simplex_hIC IA hI m σ) (c.simplex_hpnil p h_p m σ) W φ
    (c.simplexSpecι m σ) (c.simplexSpecι_base m σ) (c.simplexSpecι_open m σ)
    g hbase hquot hchart (toAbelianPresheaf (Spec (.of A)) I γS h_compatible X x₀ F)

end CechCrisCover

end
