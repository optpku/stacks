/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Action
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections.Linear
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Spec
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
import Mathlib.Tactic.CrossRefAttribute

/-!
# Products of ideal powers with scheme modules

This file constructs the subobjects obtained by applying powers of an ideal sheaf to
subobjects of scheme modules, together with their affine section descriptions and filtration
order.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The image subobject I^n 𝒢 obtained by applying the nth power of an ideal sheaf to a
subobject 𝒢 of a scheme module. -/
noncomputable def idealPowerSmulSubobject
    {ℱ : X.Modules} (I : X.IdealSheafData) (𝒢 : Subobject ℱ) (n : ℕ) : Subobject ℱ :=
  imageSubobject
    (SheafOfModules.RingedSite.IdealSheaf.action (I ^ n).toSubobject (𝒢 : X.Modules) ≫
      𝒢.arrow)

/-- The image subobject I^n ℱ obtained by applying the nth power of an ideal sheaf to a
scheme module. -/
noncomputable abbrev idealPowerProductSubobject
    (I : X.IdealSheafData) (ℱ : X.Modules) (n : ℕ) : Subobject ℱ :=
  idealPowerSmulSubobject I (⊤ : Subobject ℱ) n

namespace IdealPowerProduct

/-- Multiplication by a coefficient in `I ^ m` sends `I ^ n F` into `I ^ (m + n) F`. -/
@[stacks 02O8 "homogeneous ideal-power action factors through the product filtration"]
theorem homogeneousAction_factors
    {A : Type u} [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) {m n : ℕ} (a : (I ^ m : Ideal A)) :
    (idealPowerProductSubobject ((idealSheafDataOfIdealOnSpec I).comap f) F
        (m + n)).Factors
      ((idealPowerProductSubobject ((idealSheafDataOfIdealOnSpec I).comap f) F n).arrow ≫
        RingedSpace.globalSectionMul ((Scheme.Hom.globalSectionsMap f) a.1) F) := sorry

/-- The degree-`m` coefficient action `I ^ n F ⟶ I ^ (m + n) F`. -/
@[stacks 02O8 "homogeneous action between ideal-power products"]
noncomputable def actionMap
    {A : Type u} [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) {m n : ℕ} (a : (I ^ m : Ideal A)) :
    (idealPowerProductSubobject ((idealSheafDataOfIdealOnSpec I).comap f) F n :
      X.Modules) ⟶
      (idealPowerProductSubobject ((idealSheafDataOfIdealOnSpec I).comap f) F
        (m + n) : X.Modules) :=
  (idealPowerProductSubobject ((idealSheafDataOfIdealOnSpec I).comap f) F
    (m + n)).factorThru
      ((idealPowerProductSubobject ((idealSheafDataOfIdealOnSpec I).comap f) F n).arrow ≫
        RingedSpace.globalSectionMul ((Scheme.Hom.globalSectionsMap f) a.1) F)
      (homogeneousAction_factors I f F a)

/-- The homogeneous ideal-power action followed by the target inclusion is multiplication by the
corresponding global coefficient. -/
@[simp, stacks 02O8 "homogeneous ideal-power action inclusion formula"]
theorem actionMap_arrow
    {A : Type u} [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) {m n : ℕ} (a : (I ^ m : Ideal A)) :
    actionMap I f F a ≫
        (idealPowerProductSubobject ((idealSheafDataOfIdealOnSpec I).comap f) F
          (m + n)).arrow =
      (idealPowerProductSubobject ((idealSheafDataOfIdealOnSpec I).comap f) F n).arrow ≫
        RingedSpace.globalSectionMul ((Scheme.Hom.globalSectionsMap f) a.1) F := sorry

end IdealPowerProduct

namespace IdealPowerSmul

/-- On an affine open U, the sections of I^n 𝒢 form the submodule I(U)^n • 𝒢(U). -/
theorem sectionsSubmodule_eq_smul
    {ℱ : X.Modules} (I : X.IdealSheafData) (𝒢 : Subobject ℱ)
    [((𝒢 : X.Modules)).IsQuasicoherent] (U : X.affineOpens) (n : ℕ) :
    subobjectSectionsSubmoduleOnAffineOpen (idealPowerSmulSubobject I 𝒢 n) U =
      I.ideal U ^ n • subobjectSectionsSubmoduleOnAffineOpen 𝒢 U := sorry

end IdealPowerSmul

namespace IdealPowerProduct

/-- On an affine open U, the sections of I^n ℱ form the submodule I(U)^n • ℱ(U). -/
theorem sectionsSubmodule_eq_smul
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (I : X.IdealSheafData) (U : X.affineOpens) (n : ℕ) :
    subobjectSectionsSubmoduleOnAffineOpen (idealPowerProductSubobject I ℱ n) U =
      I.ideal U ^ n •
        (⊤ : Submodule Γ(X, U.1) (ℱ.val.obj (Opposite.op U.1))) := sorry

/-- Multiplication by successive ideal powers defines a descending filtration of every scheme
module. -/
theorem antitone
    (I : X.IdealSheafData) (ℱ : X.Modules) (n : ℕ) :
    idealPowerProductSubobject I ℱ (n + 1) ≤
      idealPowerProductSubobject I ℱ n := sorry

end IdealPowerProduct

end AlgebraicGeometry.Scheme.Modules
