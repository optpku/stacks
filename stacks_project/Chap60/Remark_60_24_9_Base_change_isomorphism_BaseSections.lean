/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap60.Remark_60_24_9_Base_change_isomorphism_Coefficients
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Exact
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Crystalline

universe u

namespace CrystallineCoefficients

variable {S X : Scheme.{u}} (I : S.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (hc : ∀ (V : S.affineOpens) (f : Γ(S, V)),
  (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
    (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
variable (x₀ : X ⟶ I.subscheme)
variable (p : ℕ) [Fact p.Prime]
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (hp : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))

/-- The base ring, lifted only to match the crystalline coefficient universe. -/
abbrev baseRing (S : Scheme.{u}) := ULift.{u + 1} Γ(S, ⊤)

/-- The base-ring map is the universe lift of pullback of global functions. -/
noncomputable def baseRingMap {S' : Scheme.{u}} (g : S ⟶ S') :
    baseRing S' →+* baseRing S :=
  ULift.ringEquiv.symm.toRingHom.comp
    ((Scheme.Hom.appTop g).hom.comp ULift.ringEquiv.toRingHom)

/-- A base function acts on a thickening by pulling back along its actual
structure morphism to the base scheme. -/
noncomputable def baseToThickening
    (T : (smallCrystallineSite S I γ hc X x₀)ᵒᵖ) :
    baseRing S →+* (liftedStructureSheaf I γ hc x₀ p s hp).obj.obj T :=
  { toFun := fun a ↦ ULift.up (Scheme.Hom.appTop T.unop.obj.1.thickeningToBase a.down)
    map_one' := sorry
    map_mul' := sorry
    map_zero' := sorry
    map_add' := sorry }

/-- Pullbacks of a fixed base function form a compatible crystalline section. -/
noncomputable def baseSectionsCone :
    Cone (liftedStructureSheaf I γ hc x₀ p s hp).obj where
  pt := RingCat.of (baseRing S)
  π :=
    { app := fun T ↦ RingCat.ofHom (baseToThickening I γ hc x₀ p s hp T)
      naturality := sorry }

/-- The actual base-ring action on crystalline global functions. Its value
at each thickening is fixed by the structure morphism, not by a ring equivalence. -/
noncomputable def baseToGlobalSections :
    baseRing S →+* RingedSite.Hom.globalSectionsRing (liftedRingedSite I γ hc x₀ p s hp) :=
  (limit.lift (liftedStructureSheaf I γ hc x₀ p s hp).obj
    (baseSectionsCone I γ hc x₀ p s hp)).hom

/-- The base action has the prescribed pullback formula on every thickening. -/
theorem baseToGlobalSections_apply
    (T : (smallCrystallineSite S I γ hc X x₀)ᵒᵖ) (a : baseRing S) :
    (limit.π (liftedStructureSheaf I γ hc x₀ p s hp).obj T)
        (baseToGlobalSections I γ hc x₀ p s hp a) =
      baseToThickening I γ hc x₀ p s hp T a := sorry

/-- Crystalline derived sections as modules over the actual base ring,
using its action through the structure morphisms of the thickenings. -/
noncomputable def baseDerivedGlobalSections
    [IsGrothendieckAbelian
      (RingedSite.ModuleCat.{u + 1} (liftedRingedSite I γ hc x₀ p s hp))] :
    RingedSite.Hom.ModuleDerived.{u + 1} (liftedRingedSite I γ hc x₀ p s hp) ⥤
      DerivedCategory (_root_.ModuleCat.{u + 1} (baseRing S)) :=
  RingedSite.Hom.moduleDerivedGlobalSections.{u + 1} (liftedRingedSite I γ hc x₀ p s hp) ⋙
    (_root_.ModuleCat.restrictScalars (baseToGlobalSections I γ hc x₀ p s hp)).mapDerivedCategory

/-- Crystalline global functions commute because all component rings of
functions on thickenings are commutative. -/
instance globalSections_commutative :
    Fact (∀ a b : RingedSite.Hom.globalSectionsRing (liftedRingedSite I γ hc x₀ p s hp),
      a * b = b * a) := ⟨sorry⟩

/-- The actual crystal coefficient placed in degree zero in the crystalline
derived category; no unrelated derived object or pointwise type equivalence
is supplied. -/
noncomputable def derivedOfCrystal
    (F : CrystallineModuleSheaf.CrisModuleSheaf S I γ hc X x₀)
    [SectionsCoherent I γ hc x₀ F] [CrystallineModuleSheaf.CrisModuleSheaf.IsCrystal F] :
    RingedSite.Hom.ModuleDerived.{u + 1} (liftedRingedSite I γ hc x₀ p s hp) :=
  (RingedSite.Hom.moduleLocalization.{u + 1} (liftedRingedSite I γ hc x₀ p s hp)).obj
    ((HomotopyCategory.singleFunctor
      (RingedSite.ModuleCat.{u + 1} (liftedRingedSite I γ hc x₀ p s hp)) (0 : ℤ)).obj
      (liftedOfCrystal I γ hc x₀ F p s hp))

end CrystallineCoefficients
