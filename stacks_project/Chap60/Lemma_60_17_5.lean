/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap60.Lemma_60_17_5_Completion
public import stacks_project.Chap60.Lemma_60_17_5_Retract
public import stacks_project.Chap60.Lemma_60_17_5_Equivalence
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf
open CrystallineConnectionPair

universe u

variable {A : Type u} [CommRing A] (p : ℕ) [Fact (Nat.Prime p)]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable (I : Ideal A) (γ : DividedPowers I)
variable {C : Type u} [CommRing C] [Algebra A C]
variable {P' : Type u} [CommRing P'] [Algebra A P']
variable (π' : P' →ₐ[A] C)
variable (hπ' : Function.Surjective π')
variable (J' : Ideal P')
variable (hJ' : J' = RingHom.ker π'.toRingHom)
variable (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C))
variable (hpnil : IsNilpotent (p : C))
variable (hIJ' : Ideal.map (algebraMap A P') I ≤ J')
variable (E' : DividedPowerEnvelope I γ (algebraMap A P') J' hIJ')
variable (hE' : DividedPowerEnvelope.IsUniversal γ (algebraMap A P') hIJ' E')
variable [Algebra.Smooth A P']

/-- Lemma 60.17.5 (1): in Situation 60.5.1, if `A → P'` is smooth and
`P' → C` is surjective with kernel `J'`, then the `p`-adic completion `D'`
of `D_{P',γ}(J')` admits a polynomial presentation `A → P → C` as in
60.17.0.1 together with divided-power `A`-algebra maps `a : D → D'` and
`b : D' → D` compatible with the maps to `C` and satisfying `a ∘ b = id_{D'}`. -/
@[stacks 07L5]
theorem exists_polynomialRetract :
    Nonempty
      (DividedPowerRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') :=
  sorry

variable (R : DividedPowerRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')

/-- Lemma 60.17.5 (2): the maps `a` and `b` induce an equivalence of
categories of pairs `(M, ∇)` satisfying (07JB)–(07JE) over `D` with the
corresponding pairs over `D'`. -/
@[stacks 07L5, instance]
instance connectionPairRetract_isEquivalence :
    (baseChangeAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R).IsEquivalence :=
  sorry

variable {S : Scheme.{u}} {IS : S.IdealSheafData}
variable {γS : ∀ V : S.affineOpens, DividedPowers (IS.ideal V)}
variable {h_compatible :
    ∀ (V : S.affineOpens) (f : Γ(S, V)),
      (γS V).IsDPMorphism (γS (S.affineBasicOpen f))
        (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
variable {X : Scheme.{u}} {x₀ : X ⟶ IS.subscheme}

/-- Lemma 60.17.5 (3): in particular, the equivalence of Proposition 60.17.4
also holds for the functor from crystals in quasi-coherent modules towards
pairs over `D'`. -/
@[stacks 07L5, instance]
instance crystalsToConnectionPairsOverSmooth_isEquivalence
    (T : smallCrystallineSite S IS γS h_compatible X x₀)
    (moduleT : ∀ F : QuasiCoherentCrystal S IS γS h_compatible X x₀,
      Module (crystallineD p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE)
        (CrisModuleSheaf.sectionModule F.obj T)) :
    (CrystallineModuleSheaf.crystalsToConnectionPairsOverSmooth p I γ π' hπ' J' hJ'
        hIC hpnil hIJ' E' hE' R T moduleT).IsEquivalence :=
  sorry

end
