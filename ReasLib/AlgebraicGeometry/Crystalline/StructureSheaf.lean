/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Site
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

variable {S : Scheme.{u}} {I : S.IdealSheafData}
  {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
  {h_compatible : ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
  {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}

/-- The crystalline structure presheaf assigns the ring of global sections of each thickening. -/
def structurePresheaf : (RelativeCRIS S I γ h_compatible X x₀)ᵒᵖ ⥤ RingCat.{u} :=
  ({ obj T := T.1.thickening
     map f := f.thickening } : RelativeCRIS S I γ h_compatible X x₀ ⥤ Scheme.{u}).op ⋙
    Scheme.Γ ⋙ forget₂ CommRingCat RingCat

/-- Global sections of thickenings satisfy descent for crystalline Zariski coverings. -/
theorem structurePresheaf_isSheaf :
    Presheaf.IsSheaf (crystallineZariskiTopology S I γ h_compatible X x₀)
      (structurePresheaf (S := S) (I := I) (γ := γ) (h_compatible := h_compatible)
        (X := X) (x₀ := x₀)) := sorry

/-- The structure sheaf of rings on the big crystalline site. -/
def structureSheaf : Sheaf (crystallineZariskiTopology S I γ h_compatible X x₀) RingCat.{u} :=
  ⟨structurePresheaf, structurePresheaf_isSheaf⟩

/-- The structure presheaf on the small crystalline site is the restriction of the big one. -/
def smallStructurePresheaf :
    (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ RingCat.{u} :=
  (smallCrystallineProperty S I γ h_compatible X x₀).ι.op ⋙ structurePresheaf

/-- Global sections of small crystalline thickenings satisfy descent for the induced topology. -/
theorem smallStructurePresheaf_isSheaf :
    Presheaf.IsSheaf (smallCrystallineZariskiTopology (S := S) (I := I) (γ := γ)
      (h_compatible := h_compatible) (X := X) (x₀ := x₀))
      (smallStructurePresheaf (S := S) (I := I) (γ := γ) (h_compatible := h_compatible)
        (X := X) (x₀ := x₀)) := sorry

/-- The structure sheaf of rings on the small crystalline site with its induced topology. -/
def smallStructureSheaf : Sheaf
    (smallCrystallineZariskiTopology (S := S) (I := I) (γ := γ)
      (h_compatible := h_compatible) (X := X) (x₀ := x₀)) RingCat.{u} :=
  ⟨smallStructurePresheaf, smallStructurePresheaf_isSheaf⟩

end AlgebraicGeometry.Scheme.Crystalline
