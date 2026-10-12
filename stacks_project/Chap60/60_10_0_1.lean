/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Sheaves.Functors
public import ReasLib.RingTheory.Localization.AtPrime.Int
public import stacks_project.Chap60.Situation_60_7_5
public import stacks_project.Chap60.«60_10_0_1_CrystallineSheaf»

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Crystalline

universe u

/-- 60.10.0.1 (1): in Situation 60.7.5, the comparison morphism on the big
crystalline site is the map from the pullback of the sheaf on the target
thickening to the sheaf on the source thickening. -/
@[stacks 07IP]
def crystallineComparison
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (g : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen g))
          (S.presheaf.map (homOfLE (S.basicOpen_le g)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (F : CrystallineSheaf.Big S I γ h_compatible X x₀)
    {A B : RelativeCRIS S I γ h_compatible X x₀}
    (f : A ⟶ B) :=
  F.comparison f

/-- The big-site comparison map is the component stored by the compatible family. -/
theorem crystallineComparison_apply
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (g : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen g))
          (S.presheaf.map (homOfLE (S.basicOpen_le g)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (F : CrystallineSheaf.Big S I γ h_compatible X x₀)
    {A B : RelativeCRIS S I γ h_compatible X x₀}
    (f : A ⟶ B) :
    crystallineComparison F f = F.comparison f :=
  sorry

/-- 60.10.0.1 (2): in Situation 60.7.5, the comparison morphism on the small
crystalline site is the map from the pullback of the sheaf on the target
thickening to the sheaf on the source thickening. -/
@[stacks 07IP]
def smallCrystallineComparison
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (g : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen g))
          (S.presheaf.map (homOfLE (S.basicOpen_le g)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (F : CrystallineSheaf.Small S I γ h_compatible X x₀)
    {A B : smallCrystallineSite S I γ h_compatible X x₀}
    (f : A ⟶ B) :=
  F.comparison f

/-- The small-site comparison map is the component stored by the compatible family. -/
theorem smallCrystallineComparison_apply
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (g : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen g))
          (S.presheaf.map (homOfLE (S.basicOpen_le g)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (F : CrystallineSheaf.Small S I γ h_compatible X x₀)
    {A B : smallCrystallineSite S I γ h_compatible X x₀}
    (f : A ⟶ B) :
    smallCrystallineComparison F f = F.comparison f :=
  sorry
