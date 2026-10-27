/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.RingTheory.DividedPowers.Extension.Construction
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Crystalline.Object
public import ReasLib.AlgebraicGeometry.Crystalline.Site
public import ReasLib.AlgebraicGeometry.Crystalline.Affine

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineObject

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {A : Type u} [CommRing A] {IA : Ideal A} (γA : DividedPowers IA)
variable {Y : Scheme.{u}} (yToS : Y ⟶ Spec.{u} (.of A))
variable (I : (Spec.{u} (.of A)).IdealSheafData)
variable (γS : ∀ V : (Spec.{u} (.of A)).affineOpens, DividedPowers (I.ideal V))
variable (h_compatible :
  ∀ (V : (Spec.{u} (.of A)).affineOpens) (f : Γ(Spec.{u} (.of A), V)),
    (γS V).IsDPMorphism (γS ((Spec.{u} (.of A)).affineBasicOpen f))
      ((Spec.{u} (.of A)).presheaf.map
        (homOfLE ((Spec.{u} (.of A)).basicOpen_le f)).op).hom)
variable (hI : Scheme.Crystalline.Affine.idealCompatible IA I)
variable (hγ : Scheme.Crystalline.Affine.dividedPowersCompatible IA γA I γS)

/-- Closed fibre `X = Y ×_S S₀` of a smooth lift `Y → Spec A` along `S₀ = V(I)`. -/
def smoothLift : Scheme.{u} :=
  pullback yToS I.subschemeι

/-- Closed immersion of the closed fibre into the smooth lift. -/
def smoothLift_inclusion : smoothLift yToS I ⟶ Y :=
  pullback.fst yToS I.subschemeι

/-- Structure map of the closed fibre over `S₀ = V(I)`. -/
def smoothLift_x₀ : smoothLift yToS I ⟶ I.subscheme :=
  pullback.snd yToS I.subschemeι

/-- Affine-section maps of a smooth morphism `Y → Spec A` are flat. -/
theorem affineSectionMap_flat [Smooth yToS] (V : Y.affineOpens) :
    (Scheme.Hom.sectionsMap yToS V).Flat :=
  sorry

/-- Image of `IA` along the affine-section map recovers the ideal of `X` in `Y`. -/
theorem affineSectionMap_map_eq_ker_ideal [Smooth yToS]
    (hI : Scheme.Crystalline.Affine.idealCompatible IA I) (V : Y.affineOpens) :
    IA.map (Scheme.Hom.sectionsMap yToS V) =
      (smoothLift_inclusion yToS I).ker.ideal V :=
  sorry

/-- Divided powers on the ideal of `X` in `Y`, obtained by uniquely extending `γA`. -/
def smoothLiftDividedPowers [Smooth yToS] (V : Y.affineOpens) :
    DividedPowers ((smoothLift_inclusion yToS I).ker.ideal V) :=
  DividedPowers.dividedPowers_ofIdealEq
    (affineSectionMap_map_eq_ker_ideal yToS I hI V)
    (DividedPowers.extensionAlong γA (Scheme.Hom.sectionsMap yToS V)
      (DividedPowers.extendsAlong_of_flat γA (Scheme.Hom.sectionsMap yToS V)
        (affineSectionMap_flat yToS V))).dividedPowers

/-- The affine-section divided powers of the smooth lift make `A → Γ(Y, V)` a
divided-power morphism, and they are the unique such extension of `γA`. -/
theorem smoothLiftDividedPowers_spec [Smooth yToS] (V : Y.affineOpens) :
    DividedPowers.IsDPMorphism γA (smoothLiftDividedPowers γA yToS I hI V)
      (Scheme.Hom.sectionsMap yToS V) :=
  sorry

/-- Uniqueness of the affine-section divided-power extension of `γA`. -/
theorem smoothLiftDividedPowers_unique [Smooth yToS] (V : Y.affineOpens)
    (δ : γA.Extension (Scheme.Hom.sectionsMap yToS V)) :
    δ.dividedPowers =
      DividedPowers.dividedPowers_ofIdealEq
        (Eq.symm (affineSectionMap_map_eq_ker_ideal yToS I hI V))
        (smoothLiftDividedPowers γA yToS I hI V) :=
  sorry

/-- Compatibility of the extended divided powers on basic opens of `Y`. -/
theorem smoothLiftDividedPowers_compatible [Smooth yToS]
    (V : Y.affineOpens) (f : Γ(Y, V)) :
    (smoothLiftDividedPowers γA yToS I hI V).IsDPMorphism
      (smoothLiftDividedPowers γA yToS I hI (Y.affineBasicOpen f))
      (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom :=
  sorry

/-- Nilpotence of `p` on `A` implies local nilpotence of `p` on the closed fibre. -/
theorem smoothLift_p_nilpotent (hpnil : IsNilpotent (p : A)) [Smooth yToS] :
    ∀ U : (smoothLift yToS I).affineOpens,
      IsNilpotent (p : Γ(smoothLift yToS I, U)) :=
  sorry


end AlgebraicGeometry.Scheme.Crystalline
