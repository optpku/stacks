/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Definition

/-!
# Finite-coefficient Galois Tate twists

This leaf owns the Tate twist `M(-1)` of a discrete continuous module, by twisting the
action by the inverse of a cyclotomic character.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Action.ModuleCat

noncomputable section

universe u v w

variable {Λ : Type u} [CommRing Λ]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} [NeZero n]

/-- The Tate-twisted action of `g` on a discrete module, multiplying the original action
by the inverse of a modular character `χ : G →* (ZMod n)ˣ`. -/
def tateTwistEnd (χ : G →* (ZMod n)ˣ) (M : DiscreteModuleCat Λ G) (g : G) :
    M.obj.V ⟶ M.obj.V :=
  ModuleCat.ofHom (LinearMap.lsmul Λ M.obj.V (((χ g)⁻¹).val.val : Λ)) ≫ M.obj.ρ g

/-- The Tate twist `M(-1)` of a discrete continuous `G`-module, with the same underlying
`Λ`-module and action `g • m = χ(g)⁻¹ • ρ(g) m`. -/
def tateTwist (χ : G →* (ZMod n)ˣ) (M : DiscreteModuleCat Λ G) : DiscreteModuleCat Λ G :=
  ⟨{ V := M.obj.V
     ρ :=
       { toFun := tateTwistEnd χ M
         map_one' := sorry
         map_mul' := sorry } },
    sorry⟩

/-- The Tate twist uses the same underlying bundled `Λ`-module as `M`. -/
theorem tateTwist_underlying (χ : G →* (ZMod n)ˣ) (M : DiscreteModuleCat Λ G) :
    (tateTwist χ M).obj.V = M.obj.V :=
  sorry

/-- The action on `tateTwist χ M` is the original action scaled by `χ(g)⁻¹`. -/
theorem tateTwist_spec (χ : G →* (ZMod n)ˣ) (M : DiscreteModuleCat Λ G) (g : G) :
    (tateTwist χ M).obj.ρ g = tateTwistEnd χ M g :=
  sorry

/-- The ring automorphism underlying an absolute Galois automorphism. -/
def absoluteGaloisToRingAut (k : Type w) [Field k] :
    Field.absoluteGaloisGroup k →* (AlgebraicClosure k ≃+* AlgebraicClosure k) where
  toFun σ := σ.toRingEquiv
  map_one' := sorry
  map_mul' := sorry

/-- The modular cyclotomic character of the absolute Galois group. -/
def galoisModularCyclotomicCharacter (k : Type w) [Field k] (n : ℕ) [NeZero n] :
    Field.absoluteGaloisGroup k →*
      (ZMod (Nat.card { x // x ∈ rootsOfUnity n (AlgebraicClosure k) }))ˣ :=
  (modularCyclotomicCharacter' (AlgebraicClosure k) n).comp (absoluteGaloisToRingAut k)

/-- The Galois Tate twist `M(-1)` of a discrete absolute Galois module, using the
modular cyclotomic character of level `n`. -/
def galoisTateTwist (k : Type w) [Field k] (n : ℕ) [NeZero n]
    (hn : Nat.card { x // x ∈ rootsOfUnity n (AlgebraicClosure k) } = n)
    (M : DiscreteModuleCat Λ (Field.absoluteGaloisGroup k)) :
    DiscreteModuleCat Λ (Field.absoluteGaloisGroup k) :=
  tateTwist ((Units.mapEquiv ((ZMod.ringEquivCongr hn).toMulEquiv)).toMonoidHom.comp
      (galoisModularCyclotomicCharacter k n)) M

/-- Unfolding of the Galois Tate twist as the character twist by the modular cyclotomic
character of level `n`. -/
theorem galoisTateTwist_spec (k : Type w) [Field k] (n : ℕ) [NeZero n]
    (hn : Nat.card { x // x ∈ rootsOfUnity n (AlgebraicClosure k) } = n)
    (M : DiscreteModuleCat Λ (Field.absoluteGaloisGroup k)) :
    galoisTateTwist k n hn M =
      tateTwist ((Units.mapEquiv ((ZMod.ringEquivCongr hn).toMulEquiv)).toMonoidHom.comp
        (galoisModularCyclotomicCharacter k n)) M :=
  sorry

