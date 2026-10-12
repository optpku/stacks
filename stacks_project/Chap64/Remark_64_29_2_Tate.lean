/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Group.ULift
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Rep.Basic
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Definition

/-!
# Tate twist of a discrete Galois module

This leaf owns the weight `-1` Tate twist of a discrete continuous
`Gal(AlgebraicClosure k / k)`-module with coefficients in a finite ring, acting
through the inverse cyclotomic character.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Action.ModuleCat
open Representation

universe u v

noncomputable section

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]
variable {Λ : Type v} [CommRing Λ] [Finite Λ]

/-- The characteristic of a finite ring divides the cardinality of its underlying additive
group. -/
theorem ringChar_dvd_card : ringChar Λ ∣ Nat.card Λ := sorry

/-- The canonical ring homomorphism `ZMod (Nat.card Λ) →+* Λ`. -/
def zmodCardCast : ZMod (Nat.card Λ) →+* Λ :=
  ZMod.castHom ringChar_dvd_card Λ

/-- Roots of unity of order `Nat.card Λ` in an algebraic closure are finite. -/
theorem finite_rootsOfUnity_algebraicClosure :
    Finite (rootsOfUnity (Nat.card Λ) (AlgebraicClosure k)) :=
  sorry

/-- The `n`th roots of unity in an algebraic closure have cardinality `n` when `n` is a
unit in the base field. -/
theorem algebraicClosure_card_rootsOfUnity
    (hΛ : IsUnit (Nat.card Λ : k)) :
    Nat.card (rootsOfUnity (Nat.card Λ) (AlgebraicClosure k)) = Nat.card Λ :=
  sorry

/-- The cyclotomic character of `Gal(AlgebraicClosure k / k)`, valued in the units of a
finite coefficient ring `Λ`. -/
def cyclotomicCharacterToUnits (hΛ : IsUnit (Nat.card Λ : k)) :
    Gal(AlgebraicClosure k / k) →* Λˣ :=
  (Units.map (zmodCardCast (Λ := Λ)).toMonoidHom).comp
    ((modularCyclotomicCharacter (AlgebraicClosure k)
        (algebraicClosure_card_rootsOfUnity (Λ := Λ) hΛ)).comp
      { toFun := fun σ : Gal(AlgebraicClosure k / k) ↦ σ.toRingEquiv
        map_one' := sorry
        map_mul' := sorry })

/-- Evaluating the `Λ`-valued cyclotomic character. -/
theorem cyclotomicCharacterToUnits_apply (hΛ : IsUnit (Nat.card Λ : k))
    (σ : Gal(AlgebraicClosure k / k)) :
    cyclotomicCharacterToUnits hΛ σ =
      (Units.map (zmodCardCast (Λ := Λ)).toMonoidHom)
        (modularCyclotomicCharacter (AlgebraicClosure k)
          (algebraicClosure_card_rootsOfUnity (Λ := Λ) hΛ) σ.toRingEquiv) :=
  sorry

/-- The Tate twist `M(-1)` of a discrete continuous Galois module: the underlying module is
unchanged, and `σ` acts by `χ_cycl(σ)⁻¹ • σ`. -/
def tateTwist (hΛ : IsUnit (Nat.card Λ : k))
    (M : DiscreteModuleCat Λ Gal(AlgebraicClosure k / k)) :
    DiscreteModuleCat Λ Gal(AlgebraicClosure k / k) :=
  ⟨{ V := M.obj.V
     ρ :=
       { toFun := fun σ ↦
           ModuleCat.ofHom
             ((cyclotomicCharacterToUnits (Λ := Λ) hΛ σ)⁻¹ • (M.obj.ρ σ).hom)
         map_one' := sorry
         map_mul' := sorry } },
    sorry⟩

/-- The underlying module of the Tate twist is the original module. -/
theorem tateTwist_carrier (hΛ : IsUnit (Nat.card Λ : k))
    (M : DiscreteModuleCat Λ Gal(AlgebraicClosure k / k)) :
    (tateTwist hΛ M).obj.V = M.obj.V :=
  sorry

/-- The Galois action on the Tate twist is scalar multiplication by the inverse cyclotomic
character composed with the original action. -/
theorem tateTwist_spec (hΛ : IsUnit (Nat.card Λ : k))
    (M : DiscreteModuleCat Λ Gal(AlgebraicClosure k / k))
    (σ : Gal(AlgebraicClosure k / k)) :
    (tateTwist hΛ M).obj.ρ σ =
      ModuleCat.ofHom
        ((cyclotomicCharacterToUnits (Λ := Λ) hΛ σ)⁻¹ • (M.obj.ρ σ).hom) :=
  sorry

/-- The `Λ`-module of invariants of a discrete continuous `G`-module. -/
def invariantsModule {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : DiscreteModuleCat Λ G) : ModuleCat.{max v u} Λ :=
  ModuleCat.of Λ ((Rep.ActionToRep Λ G).obj M.obj).ρ.invariants

/-- Unfolding of invariants as the `G`-fixed submodule of the underlying representation. -/
theorem invariantsModule_eq {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : DiscreteModuleCat Λ G) :
    invariantsModule M =
      ModuleCat.of Λ ((Rep.ActionToRep Λ G).obj M.obj).ρ.invariants :=
  sorry

/-- The `Λ`-module of coinvariants of a discrete continuous `G`-module. -/
def coinvariantsModule {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : DiscreteModuleCat Λ G) : ModuleCat.{max v u} Λ :=
  ModuleCat.of Λ (Representation.Coinvariants ((Rep.ActionToRep Λ G).obj M.obj).ρ)

/-- Unfolding of coinvariants as the quotient of the underlying representation by
`⟨g • m - m⟩`. -/
theorem coinvariantsModule_eq {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : DiscreteModuleCat Λ G) :
    coinvariantsModule M =
      ModuleCat.of Λ (Representation.Coinvariants ((Rep.ActionToRep Λ G).obj M.obj).ρ) :=
  sorry

end AlgebraicGeometry.SchemeOverField
