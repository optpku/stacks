/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Torsion
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleEmbedding
public import ReasLib.Algebra.Module.IdealPower.Predicate
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Inclusion

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace Module

variable {A : Type u} [CommRing A]

/-- Ideal-power torsion is contravariantly monotone in the ideal. -/
theorem IsIdealPowerTorsion.of_le {J K : Ideal A} (hJK : J ≤ K)
    {M : Type v} [AddCommMonoid M] [Module A M]
    (hM : IsIdealPowerTorsion K M) : IsIdealPowerTorsion J M := sorry

end Module

namespace CategoryTheory.DerivedCategory

variable {A : Type u} [CommRing A]

namespace IdealPowerTorsion

/-- Inclusion from derived modules with `K`-power-torsion cohomology to those
with `J`-power-torsion cohomology, for `J ≤ K`. -/
noncomputable def inclusionOfLE {J K : Ideal A} (hJK : J ≤ K) :
    IdealPowerTorsion K ⥤ IdealPowerTorsion J :=
  CohomologyIn.inclusion
    (fun _ hM ↦ Module.IsIdealPowerTorsion.of_le hJK hM)

/-- The inclusion `inclusionOfLE` leaves the underlying derived object unchanged. -/
theorem inclusionOfLE_obj {J K : Ideal A} (hJK : J ≤ K)
    (X : IdealPowerTorsion K) :
    ((inclusionOfLE hJK).obj X).obj = X.obj := sorry

/-- The inclusion `inclusionOfLE` leaves the underlying derived morphism unchanged. -/
theorem inclusionOfLE_map {J K : Ideal A} (hJK : J ≤ K)
    {X Y : IdealPowerTorsion K} (f : X ⟶ Y) :
    (inclusionOfLE hJK).map f =
      (CohomologyIn.inclusion
        (fun _ hM ↦ Module.IsIdealPowerTorsion.of_le hJK hM)).map f := sorry

/-- Composing `inclusionOfLE` with the ambient `J`-support inclusion is
canonically isomorphic to the ambient `K`-support inclusion. -/
noncomputable def inclusionOfLECompInclusionIso (J K : Ideal A) (hJK : J ≤ K) :
    inclusionOfLE hJK ⋙ inclusion J ≅ inclusion K :=
  CohomologyIn.inclusion.compιIso
    (fun _ hM ↦ Module.IsIdealPowerTorsion.of_le hJK hM)

end IdealPowerTorsion

namespace LocalCohomology

/-- The component of restriction from `K`-supported local cohomology to
`J`-supported local cohomology for `J ≤ K`. -/
noncomputable def supportRestrictionApp {J K : Ideal A} (hJK : J ≤ K)
    (RΓJ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion J)
    (RΓK : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion K)
    (hRΓJ : IdealPowerTorsion.inclusion J ⊣ RΓJ)
    (hRΓK : IdealPowerTorsion.inclusion K ⊣ RΓK)
    (X : DerivedCategory (ModuleCat A)) :
    (IdealPowerTorsion.inclusionOfLE hJK).obj (RΓK.obj X) ⟶ RΓJ.obj X :=
  hRΓJ.homEquiv _ _ (hRΓK.counit.app X)

/-- The components of support restriction are natural in the derived object. -/
theorem supportRestriction_naturality {J K : Ideal A} (hJK : J ≤ K)
    (RΓJ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion J)
    (RΓK : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion K)
    (hRΓJ : IdealPowerTorsion.inclusion J ⊣ RΓJ)
    (hRΓK : IdealPowerTorsion.inclusion K ⊣ RΓK)
    {X Y : DerivedCategory (ModuleCat A)} (f : X ⟶ Y) :
    (RΓK ⋙ IdealPowerTorsion.inclusionOfLE hJK).map f ≫
        supportRestrictionApp hJK RΓJ RΓK hRΓJ hRΓK Y =
      supportRestrictionApp hJK RΓJ RΓK hRΓJ hRΓK X ≫ RΓJ.map f := sorry

/-- The canonical natural restriction from `K`-supported local cohomology to
`J`-supported local cohomology for `J ≤ K`. -/
noncomputable def supportRestriction {J K : Ideal A} (hJK : J ≤ K)
    (RΓJ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion J)
    (RΓK : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion K)
    (hRΓJ : IdealPowerTorsion.inclusion J ⊣ RΓJ)
    (hRΓK : IdealPowerTorsion.inclusion K ⊣ RΓK) :
    RΓK ⋙ IdealPowerTorsion.inclusionOfLE hJK ⟶ RΓJ where
  app := supportRestrictionApp hJK RΓJ RΓK hRΓJ hRΓK
  naturality := fun _ _ f ↦
    supportRestriction_naturality hJK RΓJ RΓK hRΓJ hRΓK f

/-- The support-restriction component viewed as a morphism between the ambient
derived objects, using the canonical comparison of the two inclusions. -/
noncomputable def supportRestrictionAmbientApp {J K : Ideal A} (hJK : J ≤ K)
    (RΓJ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion J)
    (RΓK : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion K)
    (hRΓJ : IdealPowerTorsion.inclusion J ⊣ RΓJ)
    (hRΓK : IdealPowerTorsion.inclusion K ⊣ RΓK)
    (X : DerivedCategory (ModuleCat A)) :
    (IdealPowerTorsion.inclusion K).obj (RΓK.obj X) ⟶
      (IdealPowerTorsion.inclusion J).obj (RΓJ.obj X) :=
  (IdealPowerTorsion.inclusionOfLECompInclusionIso J K hJK).inv.app (RΓK.obj X) ≫
    (IdealPowerTorsion.inclusion J).map
      (supportRestrictionApp hJK RΓJ RΓK hRΓJ hRΓK X)

/-- Support restriction is characterized by factoring the `K`-support counit
through the `J`-support counit. -/
theorem supportRestriction_fac {J K : Ideal A} (hJK : J ≤ K)
    (RΓJ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion J)
    (RΓK : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion K)
    (hRΓJ : IdealPowerTorsion.inclusion J ⊣ RΓJ)
    (hRΓK : IdealPowerTorsion.inclusion K ⊣ RΓK)
    (X : DerivedCategory (ModuleCat A)) :
    supportRestrictionAmbientApp hJK RΓJ RΓK hRΓJ hRΓK X ≫ hRΓJ.counit.app X =
      hRΓK.counit.app X := sorry

/-- The degree-`i` restriction map from `K`-supported to `J`-supported local
cohomology, obtained from the ambient support-restriction morphism. -/
noncomputable def supportRestrictionMap (I J : Ideal A)
    (hI : I.FG) (hJ : J.FG)
    (M : ModuleCat A) (hM : Module.IsIdealPowerTorsion I M)
    (RΓJ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion J)
    (RΓIJ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion (I ⊔ J))
    (hRΓJ : IdealPowerTorsion.inclusion J ⊣ RΓJ)
    (hRΓIJ : IdealPowerTorsion.inclusion (I ⊔ J) ⊣ RΓIJ)
    (i : ℤ) :=
  (DerivedCategory.homologyFunctor (ModuleCat A) i).map
    (supportRestrictionAmbientApp (le_sup_right : J ≤ I ⊔ J) RΓJ RΓIJ hRΓJ hRΓIJ
      (ModuleCat.single0 M))

/-- The degreewise restriction map is an isomorphism for an `I`-power-torsion
module when the supports are `V(I) ∩ V(J)` and `V(J)`. -/
instance supportRestrictionMapIsIso (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
    (M : ModuleCat A) (hM : Module.IsIdealPowerTorsion I M)
    (RΓJ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion J)
    (RΓIJ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion (I ⊔ J))
    (hRΓJ : IdealPowerTorsion.inclusion J ⊣ RΓJ)
    (hRΓIJ : IdealPowerTorsion.inclusion (I ⊔ J) ⊣ RΓIJ) (i : ℤ) :
    IsIso (supportRestrictionMap I J hI hJ M hM RΓJ RΓIJ hRΓJ hRΓIJ i) := sorry

end LocalCohomology

end CategoryTheory.DerivedCategory
