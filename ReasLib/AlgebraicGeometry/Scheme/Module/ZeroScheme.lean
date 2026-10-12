/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.SchemeTheoreticSupport
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
import Mathlib.Tactic.CrossRefAttribute

/-!
# Zero schemes of sections of invertible modules

This file constructs the closed subscheme cut out by a global section of an invertible module
sheaf. Its ideal sheaf is the scheme-theoretic support of the cokernel of the section morphism.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- The morphism from the internal-Hom dual of an invertible module to the structure module
obtained by evaluating against a global section. -/
noncomputable def dualSectionHom
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ] (s : ℒ.sections) :
    (ihom ℒ).obj (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶
      (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  (((ρ_ ((ihom ℒ).obj (SheafOfModules.unit X.ringCatSheaf : X.Modules))).symm) ≪≫
      ((Iso.refl ((ihom ℒ).obj (SheafOfModules.unit X.ringCatSheaf : X.Modules)) ⊗ᵢ
        SheafOfModules.RingedSite.unitIsoTensorUnit
          (J := Opens.grothendieckTopology X.toTopCat) (𝒪 := X.𝒪)).symm)).hom ≫
    tensorHom (𝟙 ((ihom ℒ).obj (SheafOfModules.unit X.ringCatSheaf : X.Modules)))
      (ℒ.unitHomEquiv.symm s) ≫
    (β_ ((ihom ℒ).obj (SheafOfModules.unit X.ringCatSheaf : X.Modules)) ℒ).hom ≫
    (ihom.ev ℒ).app (SheafOfModules.unit X.ringCatSheaf : X.Modules)

/-- The ideal subobject generated as the image of the morphism obtained by evaluating the dual
of an invertible module against a global section. -/
noncomputable def zeroIdealSubobject
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ] (s : ℒ.sections) :
    X.IdealSubobject :=
  Limits.imageSubobject (dualSectionHom ℒ s)

/-- The ideal sheaf whose affine-open ideals cut out the zero scheme of a section of an
invertible module sheaf. -/
noncomputable def zeroIdealSheaf
    [MonoidalCategory X.Modules]
    (ℒ : X.Modules) [Functor.IsEquivalence (tensorRight ℒ)] (s : ℒ.sections) :
    X.IdealSheafData :=
  Scheme.Modules.schemeTheoreticSupport (Limits.cokernel (ℒ.unitHomEquiv.symm s))

/-- The zero scheme `Z(s)` of a global section `s` of an invertible module sheaf. -/
@[stacks 02OQ]
noncomputable def zeroScheme
    [MonoidalCategory X.Modules]
    (ℒ : X.Modules) [Functor.IsEquivalence (tensorRight ℒ)] (s : ℒ.sections) :
    Scheme :=
  (zeroIdealSheaf ℒ s).subscheme

/-- The canonical closed immersion `Z(s) ⟶ X`. -/
noncomputable abbrev zeroSchemeι
    [MonoidalCategory X.Modules]
    (ℒ : X.Modules) [Functor.IsEquivalence (tensorRight ℒ)] (s : ℒ.sections) :
    zeroScheme ℒ s ⟶ X :=
  (zeroIdealSheaf ℒ s).subschemeι

/-- The ideal sheaf defining the zero scheme represents the image ideal of the dual-section
morphism. -/
theorem zeroIdealSheaf_toSubobject
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ] (s : ℒ.sections) :
    (zeroIdealSheaf ℒ s).toSubobject = zeroIdealSubobject ℒ s := sorry

end AlgebraicGeometry.Scheme
