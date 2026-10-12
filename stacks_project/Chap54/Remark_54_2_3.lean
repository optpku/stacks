/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.PurelyInseparable.DeRhamMap
import StacksCheckRecall

@[expose] public section

noncomputable section

open Polynomial
open scoped TensorProduct

universe u

namespace PurelyInseparableTrace.Higher

variable (p : ℕ) (hp : p.Prime)
variable (Λ R S : Type u) [CommRing Λ] [CommRing R] [CommRing S]
variable [Algebra (ZMod p) Λ] [Algebra (ZMod p) R] [Algebra Λ R]
variable [IsScalarTower (ZMod p) Λ R] [Nontrivial R]
variable [Algebra R S] [Algebra Λ S] [IsScalarTower Λ R S]
variable (a : R) (e : S ≃ₐ[R] AdjoinRoot (X ^ p - C a))

/- Remark 54.2.3 (1): degreewise, the higher trace agrees with the canonical relative de Rham
map. -/
@[stacks 0FLF] #check (PurelyInseparableTrace.Higher.deRhamMap_apply :
  ∀ (p : ℕ) (hp : p.Prime)
    (Λ R S : Type u) [CommRing Λ] [CommRing R] [CommRing S]
    [Algebra (ZMod p) Λ] [Algebra (ZMod p) R] [Algebra Λ R]
    [IsScalarTower (ZMod p) Λ R] [Nontrivial R]
    [Algebra R S] [Algebra Λ S] [IsScalarTower Λ R S]
    (a : R) (e : S ≃ₐ[R] AdjoinRoot (X ^ p - C a)) (n : ℕ)
    (ω : KaehlerDifferential.DeRham.Form Λ S n),
    (PurelyInseparableTrace.Higher.deRhamMap p hp Λ R S a e).f n ω =
      PurelyInseparableTrace.Higher.traceOfEquiv (Λ := Λ) (R := R) p hp a e n ω)

/- Remark 54.2.3 (2): the degree-zero component of the canonical relative de Rham map is zero. -/
@[stacks 0FLF] #check (PurelyInseparableTrace.Higher.deRhamMap_degreeZero :
  ∀ (p : ℕ) (hp : p.Prime)
    (Λ R S : Type u) [CommRing Λ] [CommRing R] [CommRing S]
    [Algebra (ZMod p) Λ] [Algebra (ZMod p) R] [Algebra Λ R]
    [IsScalarTower (ZMod p) Λ R] [Nontrivial R]
    [Algebra R S] [Algebra Λ S] [IsScalarTower Λ R S]
    (a : R) (e : S ≃ₐ[R] AdjoinRoot (X ^ p - C a)),
    (PurelyInseparableTrace.Higher.deRhamMap p hp Λ R S a e).f 0 = 0)

/- Remark 54.2.3 (3): the canonical relative de Rham map commutes with wedge multiplication by a
form from `R`. -/
@[stacks 0FLF] #check (PurelyInseparableTrace.Higher.deRhamMap_wedge :
  ∀ (p : ℕ) (hp : p.Prime)
    (Λ R S : Type u) [CommRing Λ] [CommRing R] [CommRing S]
    [Algebra (ZMod p) Λ] [Algebra (ZMod p) R] [Algebra Λ R]
    [IsScalarTower (ZMod p) Λ R] [Nontrivial R]
    [Algebra R S] [Algebra Λ S] [IsScalarTower Λ R S]
    (a : R) (e : S ≃ₐ[R] AdjoinRoot (X ^ p - C a))
    (i j : ℕ)
    (η : KaehlerDifferential.DeRham.Form Λ R i)
    (ω : KaehlerDifferential.DeRham.Form Λ S j),
    (PurelyInseparableTrace.Higher.deRhamMap p hp Λ R S a e).f (i + j)
        (KaehlerDifferential.DeRham.formWedge Λ S i j
          (PurelyInseparableTrace.Higher.pullback i η ⊗ₜ ω)) =
      KaehlerDifferential.DeRham.formWedge Λ R i j
        (η ⊗ₜ (PurelyInseparableTrace.Higher.deRhamMap p hp Λ R S a e).f j ω))

end PurelyInseparableTrace.Higher
