/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Localization.Adjunction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Parasitic.Sheaf
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Closure
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated.VerdierQuotient
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.DerivedAdeq.Adjunction

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace SheafOfModules

/-- The lifted adequate-module property is a weak Serre class. -/
instance adequatePropertyIsWeakSerreClass (S : Scheme.{u}) (τ : StandardTopology) :
    ObjectProperty.IsWeakSerreClass (adequateProperty S τ) := sorry

/-- The object property selecting parasitic module sheaves on the big `τ`-site of `S`. -/
abbrev parasiticModuleProperty (S : Scheme.{u}) (τ : StandardTopology) :
    ObjectProperty
      (RingedSite.ModuleCat.{u + 1} (StandardTopology.Big.ringedSite τ S)) :=
  fun M ↦ IsParasiticOne M

/-- Membership in `parasiticModuleProperty S τ` is the parasitic-one condition. -/
theorem parasiticModuleProperty_iff (S : Scheme.{u}) (τ : StandardTopology)
    (M : RingedSite.ModuleCat.{u + 1} (StandardTopology.Big.ringedSite τ S)) :
    parasiticModuleProperty S τ M ↔ IsParasiticOne M := sorry

/-- Parasitic module sheaves form a weak Serre class. -/
instance parasiticModulePropertyIsWeakSerreClass
    (S : Scheme.{u}) (τ : StandardTopology) :
    ObjectProperty.IsWeakSerreClass (parasiticModuleProperty S τ) := sorry

namespace DerivedAdeq

/-- Derived association is full. -/
instance associatedFull (S : Scheme.{u}) (τ : StandardTopology) :
    Functor.Full (associated S τ) := sorry

/-- Derived association is faithful. -/
instance associatedFaithful (S : Scheme.{u}) (τ : StandardTopology) :
    Functor.Faithful (associated S τ) := sorry

namespace Parasitic

/-- The property of an adequate derived object having parasitic cohomology in every degree. -/
abbrev property (S : Scheme.{u}) (τ : StandardTopology) :
    ObjectProperty (DerivedAdeq S τ) :=
  (@DerivedCategory.cohomologyIn _ _ _
      (RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1}
        (StandardTopology.Big.ringedSite τ S))
      (parasiticModuleProperty S τ)).inverseImage
    (derivedAdequateProperty S τ).ι

/-- An adequate derived object is parasitic exactly when all its homology modules are
parasitic one. -/
theorem property_iff (S : Scheme.{u}) (τ : StandardTopology) (K : DerivedAdeq S τ) :
    property S τ K ↔
      ∀ n : ℤ, IsParasiticOne
        ((@DerivedCategory.homologyFunctor
          (RingedSite.ModuleCat.{u + 1} (StandardTopology.Big.ringedSite τ S)) _ _
          (RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1}
            (StandardTopology.Big.ringedSite τ S)) n).obj K.obj) := sorry

/-- The kernel of derived Zariski restriction consists exactly of the adequate derived
objects with parasitic cohomology. -/
theorem kernel_eq (S : Scheme.{u}) (τ : StandardTopology) :
    Functor.kernel (zariskiRestriction S τ) = property S τ := sorry

/-- Derived Zariski restriction is the localization at the Verdier system determined by
parasitic cohomology. -/
instance zariskiRestrictionIsLocalization (S : Scheme.{u}) (τ : StandardTopology) :
    (zariskiRestriction S τ).IsLocalization (property S τ).trW := sorry

/-- The Verdier quotient by adequate derived objects with parasitic cohomology is
equivalent to the derived category of quasicoherent sheaves. -/
noncomputable def equivalence (S : Scheme.{u}) (τ : StandardTopology) :
    ObjectProperty.verdierQuotient (property S τ) ≌ Scheme.DerivedQCoh S :=
  Localization.uniq (property S τ).trW.Q (zariskiRestriction S τ)
    (property S τ).trW

/-- Under `equivalence S τ`, the Verdier quotient functor agrees with derived Zariski
restriction. -/
noncomputable def quotientCompIso (S : Scheme.{u}) (τ : StandardTopology) :
    ObjectProperty.verdierQuotientFunctor (property S τ) ⋙
        (equivalence S τ).functor ≅ zariskiRestriction S τ :=
  Localization.compUniqFunctor
    (property S τ).trW.Q (zariskiRestriction S τ) (property S τ).trW

/-- The Verdier quotient functor sends the association--restriction counit at `X` to an
isomorphism. -/
instance counitIsIso (S : Scheme.{u}) (τ : StandardTopology) (X : DerivedAdeq S τ) :
    IsIso ((ObjectProperty.verdierQuotientFunctor (property S τ)).map
      ((adjunction S τ).counit.app X)) := sorry

/-- The equivalence with derived quasicoherent sheaves identifies morphisms in the Verdier
quotient with morphisms after derived Zariski restriction. -/
noncomputable def homEquiv (S : Scheme.{u}) (τ : StandardTopology)
    (X Y : DerivedAdeq S τ) :
    ((ObjectProperty.verdierQuotientFunctor (property S τ)).obj X ⟶
        (ObjectProperty.verdierQuotientFunctor (property S τ)).obj Y) ≃
      ((zariskiRestriction S τ).obj X ⟶ (zariskiRestriction S τ).obj Y) :=
  (equivalence S τ).fullyFaithfulFunctor.homEquiv.trans
    (Iso.homCongr ((quotientCompIso S τ).app X) ((quotientCompIso S τ).app Y))

/-- Applying `homEquiv` maps a quotient morphism through `equivalence` and transports it
along `quotientCompIso`. -/
theorem homEquiv_apply (S : Scheme.{u}) (τ : StandardTopology)
    (X Y : DerivedAdeq S τ)
    (f : (ObjectProperty.verdierQuotientFunctor (property S τ)).obj X ⟶
      (ObjectProperty.verdierQuotientFunctor (property S τ)).obj Y) :
    homEquiv S τ X Y f =
      (quotientCompIso S τ).inv.app X ≫
        (equivalence S τ).functor.map f ≫
          (quotientCompIso S τ).hom.app Y := sorry

end Parasitic

end DerivedAdeq

end SheafOfModules

end
