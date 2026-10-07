module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.RingTheory.PicardGroup
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.TensorPower
public import ReasLib.RingTheory.Polynomial.Equalizer

/-!
# Equal-endpoint Milnor lines

The equal-endpoint polynomial algebra and its clutching-ratio submodules give
an explicit family of invertible scheme modules with sections in both tensor
directions.
-/

@[expose] public section

noncomputable section

universe u

open Polynomial
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.EqualEndpoint

/-- The affine scheme spectrum of the equal-endpoint polynomial algebra. -/
def scheme (k : Type u) [Field k] : Scheme.{u} :=
  Spec (CommRingCat.of (equalEndpoint k))

/-- The Milnor line of clutching ratio `u`, consisting of polynomials whose
endpoint values have ratio `u`. -/
def milnorLine (k : Type u) [Field k] (u : kˣ) :
    Submodule (equalEndpoint k) (Polynomial k) where
  carrier := {f | f.eval 1 = (u : k) * f.eval 0}
  zero_mem' := by
    change (0 : Polynomial k).eval 1 = (u : k) * (0 : Polynomial k).eval 0
    simp
  add_mem' := by
    intro f g hf hg
    change f.eval 1 = (u : k) * f.eval 0 at hf
    change g.eval 1 = (u : k) * g.eval 0 at hg
    change (f + g).eval 1 = (u : k) * (f + g).eval 0
    simp only [Polynomial.eval_add]
    rw [hf, hg]
    ring
  smul_mem' := by
    intro a f hf
    change f.eval 1 = (u : k) * f.eval 0 at hf
    change ((a : Polynomial k) * f).eval 1 = (u : k) * ((a : Polynomial k) * f).eval 0
    rw [Polynomial.eval_mul, Polynomial.eval_mul, hf]
    have ha : (a : Polynomial k).eval 0 = (a : Polynomial k).eval 1 :=
      (Polynomial.mem_equalEndpoint (R := k) (a : Polynomial k)).mp a.property
    rw [← ha]
    ring

/-- Membership in a Milnor line is characterized by the endpoint-ratio equation. -/
theorem mem_milnorLine {k : Type u} [Field k] {u : kˣ} {f : Polynomial k} :
    f ∈ milnorLine k u ↔ f.eval 1 = (u : k) * f.eval 0 := sorry

/-- The conductor polynomial belongs to every Milnor line. -/
theorem conductor_mem_milnorLine (k : Type u) [Field k] (u : kˣ) :
    (X ^ 2 - X : Polynomial k) ∈ milnorLine k u := sorry

/-- Every Milnor line is a nontrivial module. -/
theorem milnorLine_nontrivial (k : Type u) [Field k] (u : kˣ) :
    Nontrivial (milnorLine k u) := sorry

/-- Every Milnor line is invertible over the equal-endpoint polynomial algebra. -/
theorem milnorLine_invertible (k : Type u) [Field k] (u : kˣ) :
    Module.Invertible (equalEndpoint k) (milnorLine k u) := sorry

/-- The associated sheaf of a Milnor line on its equal-endpoint scheme. -/
def lineBundle (k : Type u) [Field k] (u : kˣ) : (scheme k).Modules :=
  tilde (ModuleCat.of (CommRingCat.of (equalEndpoint k)) (milnorLine k u))

/-- The associated Milnor line sheaf is invertible. -/
instance instLineBundleInvertible (k : Type u) [Field k] (u : kˣ) :
    Invertible (lineBundle k u) := sorry

/-- A nontrivial clutching ratio gives a line bundle not isomorphic to the unit module. -/
theorem lineBundle_not_isomorphic_unit (k : Type u) [Field k] (u : kˣ) (h_ne_one : u ≠ 1) :
    ¬ Nonempty (lineBundle k u ≅ 𝟙_ (scheme k).Modules) := sorry

/-- The global sections of every Milnor line sheaf are nontrivial. -/
theorem globalSections_nontrivial (k : Type u) [Field k] (u : kˣ) :
    Nontrivial Γ(lineBundle k u, ⊤) := sorry

/-- The global sections of the inverse tensor power of every Milnor line sheaf
are nontrivial. -/
theorem inverseGlobalSections_nontrivial (k : Type u) [Field k] (u : kˣ) :
    Nontrivial Γ(tensorPowerInt (lineBundle k u) (-1), ⊤) := sorry

/-- The Milnor line sheaf of ratio `-1` on the rational equal-endpoint scheme is
nontrivial and invertible, with nontrivial global sections for itself and its
inverse tensor power. -/
theorem rationalMilnorLineExample :
    Invertible (lineBundle ℚ (-1 : ℚˣ)) ∧
      ¬ Nonempty (lineBundle ℚ (-1 : ℚˣ) ≅ 𝟙_ (scheme ℚ).Modules) ∧
      Nontrivial Γ(lineBundle ℚ (-1 : ℚˣ), ⊤) ∧
      Nontrivial Γ(tensorPowerInt (lineBundle ℚ (-1 : ℚˣ)) (-1), ⊤) := sorry

end AlgebraicGeometry.EqualEndpoint
