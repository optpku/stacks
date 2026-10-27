/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.AlgebraicGeometry.Crystalline.Cech.Evaluation
public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.RingTheory.Ideal.Prod

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

variable (E : CechCrisEnvelope p IA γA c)

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

/-- Product ring map `D(n) → D(m)` induced by envelope functoriality. -/
noncomputable def cechDHom {n m : SimplexCategory} (f : n ⟶ m) :
    E.cechD n.len →+* E.cechD m.len :=
  RingHom.pi fun σ =>
    (E.homD f σ).comp (Pi.evalRingHom _ (reindex f σ))

/-- The distinguished ideal of the product ring is the product of the completed envelope ideals. -/
def cechDPIdeal (n : ℕ) : Ideal (E.cechD n) :=
  Ideal.pi fun σ ↦
    (envelopeCompletionRing p A (c.simplexPolynomial n σ) IA γA
      (c.simplexKernel n σ) (E.hIJ n σ) (E.E n σ) (E.N n σ) (E.hN n σ)
      (E.γhat n σ)).ideal

/-- Divided powers on the product ideal act componentwise, and vanish outside that ideal. -/
def cechDDividedPowers (n : ℕ) : DividedPowers (E.cechDPIdeal n) where
  dpow k x := @ite (E.cechD n) (x ∈ E.cechDPIdeal n) (Classical.propDecidable _)
    (fun σ ↦ (E.γhat n σ).dpow k (x σ)) 0
  dpow_null := sorry
  dpow_zero := sorry
  dpow_one := sorry
  dpow_mem := sorry
  dpow_add := sorry
  dpow_mul := sorry
  mul_dpow := sorry
  dpow_comp := sorry

/-- The degreewise product of completed simplex divided-power rings. -/
def cechDPRing (n : ℕ) : DividedPowerRing.{u} :=
  DividedPowerRing.of (E.cechD n) (E.cechDPIdeal n) (E.cechDDividedPowers n)

/-- The completed simplex envelopes form a cosimplicial divided-power ring. -/
def cechDPCosimplicial : CosimplicialObject DividedPowerRing.{u} where
  obj n := E.cechDPRing n.len
  map {_ _} f :=
    { toRingHom := E.cechDHom f
      ideal_comp := sorry
      dpow_comp := sorry }
  map_id := sorry
  map_comp := sorry

/-- Forgetting divided powers gives the cosimplicial product ring. -/
def cechDCosimplicial : CosimplicialObject CommRingCat.{u} :=
  E.cechDPCosimplicial ⋙ DividedPowerRing.forgetCommRing

variable (s : Spec.{u} (.of A) ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
variable (hI : Affine.idealCompatible IA I) (hγ : Affine.dividedPowersCompatible IA γA I γS)
variable [HasLimits AddCommGrpCat.{u}]

/-- The completed envelope at a simplex, with its quotient to the chart. -/
abbrev completedSimplex (n : ℕ) (σ : Fin (n + 1) → c.Λ) :=
  c.simplexCrisObject n σ h_p (E.hIJ n σ) (E.E n σ) (E.hE n σ) (E.N n σ) (E.hN n σ)
    (E.γhat n σ) (envelopeCompletionDividedPowers_isDPMorphism (E.E n σ) (E.N n σ) (E.hN n σ))

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
  (X.presheaf.map (homOfLE (c.simplexOpen_reindex_le (SimplexCategory.Hom.toOrderHom f) σ)).op).hom

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
      (E.γhat n σ) (envelopeCompletionDividedPowers_isDPMorphism (E.E n σ) (E.N n σ) (E.hN n σ))

/-- The degree-`n` module is the product of simplex values of `F`. -/
theorem cechM_obj
    (F : CrisModuleSheaf (Spec (.of A)) I γS h_compatible X x₀) (n : ℕ) :
    E.cechM s h_p hI hγ F n =
      ∀ σ : Fin (n + 1) → c.Λ,
        c.simplexModule hI hγ F n σ s h_p (E.hIJ n σ) (E.E n σ) (E.hE n σ) (E.N n σ) (E.hN n σ)
          (E.γhat n σ) (envelopeCompletionDividedPowers_isDPMorphism (E.E n σ) (E.N n σ) (E.hN n σ)) :=
  rfl

/-- The degreewise product of completed simplex coefficient modules. -/
def cechMModule
    (F : CrisModuleSheaf (Spec (.of A)) I γS h_compatible X x₀) (n : ℕ) :
    ModuleCat.{u} (E.cechD n) :=
  @ModuleCat.of (E.cechD n) _ (E.cechM s h_p hI hγ F n) _
    (@Pi.module' (Fin (n + 1) → c.Λ)
      (fun σ ↦ envelopeCompletionRing p A (c.simplexPolynomial n σ) IA γA
        (c.simplexKernel n σ) (E.hIJ n σ) (E.E n σ) (E.N n σ) (E.hN n σ) (E.γhat n σ))
      (fun σ ↦ c.simplexModule hI hγ F n σ s h_p (E.hIJ n σ) (E.E n σ) (E.hE n σ)
        (E.N n σ) (E.hN n σ) (E.γhat n σ)
        (envelopeCompletionDividedPowers_isDPMorphism (E.E n σ) (E.N n σ) (E.hN n σ)))
      _ _ (fun σ ↦ c.simplexModuleStructure hI hγ F n σ s h_p (E.hIJ n σ) (E.E n σ)
        (E.hE n σ) (E.N n σ) (E.hN n σ) (E.γhat n σ)
        (envelopeCompletionDividedPowers_isDPMorphism (E.E n σ) (E.N n σ) (E.hN n σ))))

/-- Scalar multiplication on degreewise Čech coefficients is the product action. -/
def cechMSmul
    (F : CrisModuleSheaf (Spec (.of A)) I γS h_compatible X x₀) (n : ℕ)
    (r : E.cechD n) (m : E.cechM s h_p hI hγ F n) : E.cechM s h_p hI hγ F n :=
  (E.cechMModule s h_p hI hγ F n).isModule.smul r m

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

/-- Čech coefficient comparison maps are semilinear along the product envelope maps. -/
theorem cechMHom_smul
    (F : CrisModuleSheaf (Spec (.of A)) I γS h_compatible X x₀)
    {n m : SimplexCategory} (f : n ⟶ m)
    (r : E.cechD n.len) (x : E.cechM s h_p hI hγ F n.len) :
    E.cechMHom s h_p hI hγ F f (E.cechMSmul s h_p hI hγ F n.len r x) =
      E.cechMSmul s h_p hI hγ F m.len (E.cechDHom f r)
        (E.cechMHom s h_p hI hγ F f x) := sorry

/-- Cosimplicial abelian group `M(*)`. -/
noncomputable def cechMCosimplicial
    (F : CrisModuleSheaf (Spec (.of A)) I γS h_compatible X x₀) :
    CosimplicialObject AddCommGrpCat.{u} where
  obj n := AddCommGrpCat.of (E.cechM s h_p hI hγ F n.len)
  map {_ _} f := AddCommGrpCat.ofHom (E.cechMHom s h_p hI hγ F f)
  map_id := sorry
  map_comp := sorry

/-- The Čech coefficients form a presheaf of modules on the opposite simplex category,
with the specified product action and the existing abelian cosimplicial object. -/
def cechModule
    (F : CrisModuleSheaf (Spec (.of A)) I γS h_compatible X x₀) :
    PresheafOfModules
      ((opOpEquivalence SimplexCategory).functor ⋙ E.cechDCosimplicial ⋙
        forget₂ CommRingCat RingCat) :=
  @PresheafOfModules.ofPresheaf SimplexCategoryᵒᵖ _
    ((opOpEquivalence SimplexCategory).functor ⋙ E.cechDCosimplicial ⋙
      forget₂ CommRingCat RingCat)
    ((opOpEquivalence SimplexCategory).functor ⋙ E.cechMCosimplicial s h_p hI hγ F)
    (fun n ↦ (E.cechMModule s h_p hI hγ F n.unop.unop.len).isModule)
    (fun {_ _} f r m ↦ E.cechMHom_smul s h_p hI hγ F f.unop.unop r m)

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
      (AddCommGrpCat.of (E.cechM s h_p hI hγ F n)) := sorry


end CechCrisEnvelope

end EnvelopeMaps

end
