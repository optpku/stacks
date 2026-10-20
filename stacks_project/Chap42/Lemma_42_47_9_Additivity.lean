/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap42.Lemma_42_35_4_Additive
public import ReasLib.AlgebraicGeometry.ChowCohomology.Completion.Integral
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Biproduct
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Derived.Biproduct
public import ReasLib.AlgebraicGeometry.BivariantClass.LocalizedExtension.Additive

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect

/- A binary biproduct of perfect derived modules is perfect. -/
#check (AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect.biprod :
    ∀ {X : RingedSpace.{u}} {E F : ModuleDerived X}
    (hE : ModuleDerived.IsPerfect E) (hF : ModuleDerived.IsPerfect F),
    ModuleDerived.IsPerfect (E ⊞ F))

end AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect

namespace AlgebraicGeometry.ChernClass.Derived.IsDefined

/- Chern classes are defined for a binary biproduct when they are defined for both summands. -/
#check (AlgebraicGeometry.ChernClass.Derived.IsDefined.biprod :
    ∀ {X : Scheme.{u}} {E F : RingedSpace.ModuleDerived X.toRingedSpace}
    (hE : IsDefined E) (hF : IsDefined F),
    IsDefined (E ⊞ F))

end AlgebraicGeometry.ChernClass.Derived.IsDefined

namespace AlgebraicGeometry.ChernClass.Derived

/- Newton classes of perfect derived modules are additive under binary biproducts. -/
#check (AlgebraicGeometry.ChernClass.Derived.newtonClass_biprod :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta]
    (pi : X ⟶ S) [LocallyOfFiniteType pi] (classes : Theory delta pi)
    {E F : RingedSpace.ModuleDerived X.toRingedSpace}
    (perfectE : RingedSpace.ModuleDerived.IsPerfect E)
    (perfectF : RingedSpace.ModuleDerived.IsPerfect F)
    (definedE : IsDefined E) (definedF : IsDefined F) (p : ℕ),
    newtonClass delta pi classes (E ⊞ F) (perfectE.biprod perfectF)
        (definedE.biprod definedF) p =
      BivariantClass.pointwiseAdd delta (𝟙 (Over.mk pi)) (p : ℤ)
        (newtonClass delta pi classes E perfectE definedE p)
        (newtonClass delta pi classes F perfectF definedF p))

end AlgebraicGeometry.ChernClass.Derived

namespace AlgebraicGeometry.BivariantClass.IsLocalizedExtension

/- The sum of two localized extensions is a localized extension of the sum. -/
#check (AlgebraicGeometry.BivariantClass.IsLocalizedExtension.add :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] {delta : S → ℤ}
    [IsDimensionFunction delta] {X : Over S} [LocallyOfFiniteType X.hom]
    {X₁ X₂ : Scheme.{u}} {i₁ : X₁ ⟶ X.left} {i₂ : X₂ ⟶ X.left}
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] {p : ℤ}
    {ambientE ambientF : BivariantClass delta (𝟙 (Over.mk (i₂ ≫ X.hom))) p}
    {localizedE localizedF : BivariantClass delta
      (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) p}
    (hE : IsLocalizedExtension delta X i₁ i₂ p ambientE localizedE)
    (hF : IsLocalizedExtension delta X i₁ i₂ p ambientF localizedF),
    IsLocalizedExtension delta X i₁ i₂ p
      (BivariantClass.pointwiseAdd delta (𝟙 (Over.mk (i₂ ≫ X.hom))) p
        ambientE ambientF)
      (BivariantClass.pointwiseAdd delta
        (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) p localizedE localizedF))

end AlgebraicGeometry.BivariantClass.IsLocalizedExtension
