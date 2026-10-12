/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReasLib.RingTheory.Localization.AtPrime.Int
public import stacks_project.Chap60.«60_10_0_2_ModuleSheaf»
public import stacks_project.Chap60.Situation_60_7_5

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/-- 60.10.0.2: for a morphism `f` of crystalline objects and a crystalline module sheaf `F`,
the comparison morphism `c_f` has type
`(Scheme.Modules.pullback f.thickening).obj (F.obj B) ⟶ F.obj A`. -/
@[stacks 07IQ]
def crystallineModuleComparison
    (p : ℕ) [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (g : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen g))
          (S.presheaf.map (homOfLE (S.basicOpen_le g)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (F : CrystallineModuleSheaf S I γ h_compatible X x₀)
    {A B : CRIS S I γ h_compatible X x₀}
    (f : CrystallineObject.Hom A B) :
    (Scheme.Modules.pullback f.thickening).obj (F.obj B) ⟶ F.obj A :=
  F.comparison f

/-- The source-facing comparison map is the component stored by the crystalline module sheaf. -/
lemma crystallineModuleComparison_apply
    (p : ℕ) [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (g : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen g))
          (S.presheaf.map (homOfLE (S.basicOpen_le g)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (F : CrystallineModuleSheaf S I γ h_compatible X x₀)
    {A B : CRIS S I γ h_compatible X x₀}
    (f : CrystallineObject.Hom A B) :
    crystallineModuleComparison p S I γ h_compatible s X x₀ h_p F f = F.comparison f := sorry
