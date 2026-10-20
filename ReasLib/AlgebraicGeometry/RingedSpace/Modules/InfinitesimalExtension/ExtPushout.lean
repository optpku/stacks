/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension.Ext
public import ReasLib.AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension.Pushout

/-!
# Pushouts and Ext¹ classes of infinitesimal extensions

For compatible trivializations of first-order thickenings, the canonical pushout on
isomorphism classes of infinitesimal extensions commutes with restriction to Ext¹ classes
and postcomposition along the kernel comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Abelian (Ext)
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.IsFirstOrderThickening
open AlgebraicGeometry.RingedSpace.Modules
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Modules
namespace InfinitesimalExtension

variable {X X1 X2 : RingedSpace.{u}} {i1 : X ⟶ X1}
variable [IsFirstOrderThickening i1]
variable {h : X1 ⟶ X2} [IsFirstOrderThickening (i1 ≫ h)]

/-- Pushout along a compatible kernel comparison and morphism of first-order thickenings
descends to isomorphism classes of infinitesimal extensions. -/
def pushoutOnIsoClass {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSq c1 c2 κ) :
    IsoClass (i1 ≫ h) F K2 c2 → IsoClass i1 F K1 c1 :=
  Quotient.map (pushout c1 κ hc) fun E₁ E₂ hE ↦ by
    obtain ⟨φ⟩ := (hE : Nonempty (Hom E₁ E₂))
    exact ⟨pushoutMap c1 κ hc φ⟩

/-- The pushout on isomorphism classes sends the class of a representative to the class
of its canonical pushout. -/
theorem pushoutOnIsoClass_mk {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSq c1 c2 κ)
    (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2) :
    pushoutOnIsoClass c1 κ hc (IsoClass.mk F'2) = IsoClass.mk (pushout c1 κ hc F'2) := rfl

variable (τ1 : Trivialization i1) (τ2 : Trivialization (i1 ≫ h))

/-- For compatible trivializations, the Ext¹ class of a pushed-out infinitesimal extension
is the postcomposition of the original class along the kernel comparison. -/
theorem extClass_pushout [HasExt.{u} X.Modules] {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSq c1 c2 κ)
    (retraction_comm : h ≫ τ2.retraction = τ1.retraction)
    (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2) :
    extClass τ1 (pushout c1 κ hc F'2) =
      (Ext.mk₀ κ).postcomp F (add_zero 1) (extClass τ2 F'2) := sorry

/-- For compatible trivializations, restriction to Ext¹ classes commutes with the canonical
pushout on isomorphism classes and postcomposition along the kernel comparison. -/
theorem extClassOnIsoClass_pushout [HasExt.{u} X.Modules] {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSq c1 c2 κ)
    (retraction_comm : h ≫ τ2.retraction = τ1.retraction)
    (p : IsoClass (i1 ≫ h) F K2 c2) :
    extClassOnIsoClass τ1 c1 (pushoutOnIsoClass c1 κ hc p) =
      (Ext.mk₀ κ).postcomp F (add_zero 1) (extClassOnIsoClass τ2 c2 p) := sorry

end InfinitesimalExtension
end AlgebraicGeometry.RingedSpace.Modules
