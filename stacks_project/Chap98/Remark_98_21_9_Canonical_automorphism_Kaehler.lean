/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic
public import stacks_project.Chap98.Lemma_98_21_2_Lifts

/-!
# Canonical sections of `B[Ω_{B/A}]`

The two ring maps `B ⟶ B[Ω_{B/A}]` given by `b ↦ (b, d_{B/A}(b))` and by the
first-summand inclusion, together with the automorphism `τ` of `B[Ω_{B/A}]`
satisfying `τ ∘ inl = can`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open TrivSqZeroExt
open CommRingCat (KaehlerDifferential)

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {A B : CommRingCat.{u}} (v : A ⟶ B)

/-- The module of Kähler differentials `Ω_{B/A}` as an object of `ModuleCat B`. -/
def kaehlerObj : ModuleCat.{u} B :=
  CommRingCat.KaehlerDifferential v

/-- `kaehlerObj v` is `CommRingCat.KaehlerDifferential v`. -/
theorem kaehlerObj_eq : kaehlerObj v = CommRingCat.KaehlerDifferential v := sorry

/-- The universal derivation `d_{B/A}` as a map into `kaehlerObj v`. -/
def kaehlerD (b : B) : kaehlerObj v :=
  KaehlerDifferential.d b

/-- The universal derivation vanishes on the image of `A ⟶ B`. -/
theorem kaehlerD_algebraMap (a : A) : kaehlerD v (v.hom a) = 0 := sorry

/-- The source ring map `B ⟶ B[Ω_{B/A}]` sending `b` to `inl b + inr (d_{B/A} b)`. -/
def trivSqZeroCan : B ⟶ trivSqZero B (kaehlerObj v) :=
  CommRingCat.ofHom
    { toFun b := inl b + inr (kaehlerD v b)
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry }

/-- Evaluating `trivSqZeroCan v` on `b` yields `inl b + inr (d_{B/A} b)`. -/
theorem trivSqZeroCan_apply (b : B) :
    (trivSqZeroCan v).hom b = inl b + inr (kaehlerD v b) := sorry

/-- `trivSqZeroCan v` is a section of the coefficient projection `B[Ω_{B/A}] ⟶ B`. -/
theorem trivSqZeroCan_comp_fst :
    trivSqZeroCan v ≫ trivSqZeroHom B (kaehlerObj v) = 𝟙 B := sorry

/-- The two sections `can` and `inl` agree after precomposition with `A ⟶ B`,
since `d_{B/A}` vanishes on the image of `A`. -/
theorem trivSqZeroCan_comp_algebraMap :
    v ≫ trivSqZeroCan v = v ≫ trivSqZeroInl B (kaehlerObj v) := sorry

/-- The automorphism `τ` of `B[Ω_{B/A}]` sending `(b, ω)` to `(b, ω + d_{B/A} b)`. -/
def trivSqZeroTau : trivSqZero B (kaehlerObj v) ⟶ trivSqZero B (kaehlerObj v) :=
  CommRingCat.ofHom
    { toFun x := inl x.fst + inr (x.snd + kaehlerD v x.fst)
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry }

/-- Evaluating `trivSqZeroTau v` on `x` yields `inl x.fst + inr (x.snd + d_{B/A} x.fst)`. -/
theorem trivSqZeroTau_apply (x : trivSqZero B (kaehlerObj v)) :
    (trivSqZeroTau v).hom x = inl x.fst + inr (x.snd + kaehlerD v x.fst) :=
  sorry

/-- The identity `τ ∘ inl = can`. -/
theorem trivSqZeroTau_comp_inl :
    trivSqZeroInl B (kaehlerObj v) ≫ trivSqZeroTau v = trivSqZeroCan v := sorry

/-- The inverse automorphism `τ⁻¹` of `B[Ω_{B/A}]` sending `(b, ω)` to
`(b, ω - d_{B/A} b)`. -/
def trivSqZeroTauInv : trivSqZero B (kaehlerObj v) ⟶ trivSqZero B (kaehlerObj v) :=
  CommRingCat.ofHom
    { toFun x := inl x.fst + inr (x.snd - kaehlerD v x.fst)
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry }

/-- Evaluating `trivSqZeroTauInv v` on `x` yields
`inl x.fst + inr (x.snd - d_{B/A} x.fst)`. -/
theorem trivSqZeroTauInv_apply (x : trivSqZero B (kaehlerObj v)) :
    (trivSqZeroTauInv v).hom x =
      inl x.fst + inr (x.snd - kaehlerD v x.fst) := sorry

/-- The identity `τ⁻¹ ∘ can = inl`. -/
theorem trivSqZeroTauInv_comp_can :
    trivSqZeroCan v ≫ trivSqZeroTauInv v = trivSqZeroInl B (kaehlerObj v) := sorry

/-- `τ` and `τ⁻¹` are inverse ring maps. -/
theorem trivSqZeroTau_comp_inv :
    trivSqZeroTau v ≫ trivSqZeroTauInv v = 𝟙 (trivSqZero B (kaehlerObj v)) := sorry

/-- `τ⁻¹` and `τ` are inverse ring maps. -/
theorem trivSqZeroTauInv_comp_tau :
    trivSqZeroTauInv v ≫ trivSqZeroTau v = 𝟙 (trivSqZero B (kaehlerObj v)) := sorry

variable {S : Scheme.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}

/-- Both sections `B ⟶ B[Ω_{B/A}]` induce the same structure morphism
`Spec(B[Ω_{B/A}]) ⟶ S` once `Spec(B) ⟶ S` is induced from `A`. -/
theorem trivSqZeroCan_spec (hv : Spec.map v ≫ σA = σB) :
    Spec.map (trivSqZeroCan v) ≫ σB = specTrivSqZero σB (kaehlerObj v) := sorry

/-- The morphism in `Over S` associated with `b ↦ (b, d_{B/A} b)`. -/
def specOverCan (hv : Spec.map v ≫ σA = σB) :
    Over.mk (specTrivSqZero σB (kaehlerObj v)) ⟶ Over.mk σB :=
  specOverHom (trivSqZeroCan v) (trivSqZeroCan_spec v hv)

/-- The left component of `specOverCan` is `Spec.map (trivSqZeroCan v)`. -/
theorem specOverCan_left (hv : Spec.map v ≫ σA = σB) :
    (specOverCan v hv).left = Spec.map (trivSqZeroCan v) := sorry

/-- `τ` is compatible with the structure morphism of `Spec(B[Ω_{B/A}])`. -/
theorem trivSqZeroTau_spec (hv : Spec.map v ≫ σA = σB) :
    Spec.map (trivSqZeroTau v) ≫ specTrivSqZero σB (kaehlerObj v) =
      specTrivSqZero σB (kaehlerObj v) := sorry

/-- The morphism in `Over S` associated with `τ`. -/
def specOverTau (hv : Spec.map v ≫ σA = σB) :
    Over.mk (specTrivSqZero σB (kaehlerObj v)) ⟶
      Over.mk (specTrivSqZero σB (kaehlerObj v)) :=
  specOverHom (trivSqZeroTau v) (trivSqZeroTau_spec v hv)

/-- `τ ∘ inl = can` as morphisms in `Over S`. -/
theorem specOverTau_comp_inl (hv : Spec.map v ≫ σA = σB) :
    specOverTau v hv ≫ specOverInl σB (kaehlerObj v) = specOverCan v hv := sorry

/-- `τ⁻¹` is compatible with the structure morphism of `Spec(B[Ω_{B/A}])`. -/
theorem trivSqZeroTauInv_spec (hv : Spec.map v ≫ σA = σB) :
    Spec.map (trivSqZeroTauInv v) ≫ specTrivSqZero σB (kaehlerObj v) =
      specTrivSqZero σB (kaehlerObj v) := sorry

/-- The morphism in `Over S` associated with `τ⁻¹`. -/
def specOverTauInv (hv : Spec.map v ≫ σA = σB) :
    Over.mk (specTrivSqZero σB (kaehlerObj v)) ⟶
      Over.mk (specTrivSqZero σB (kaehlerObj v)) :=
  specOverHom (trivSqZeroTauInv v) (trivSqZeroTauInv_spec v hv)

/-- `τ⁻¹ ∘ can = inl` as morphisms in `Over S`. -/
theorem specOverTauInv_comp_can (hv : Spec.map v ≫ σA = σB) :
    specOverTauInv v hv ≫ specOverCan v hv = specOverInl σB (kaehlerObj v) := sorry

end AlgebraicGeometry.GroupoidsOver
