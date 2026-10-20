module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Point
public import ReasLib.AlgebraicGeometry.RingedSpace.Skyscraper
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stalks of module sheaves on a ringed point

The stalk of the module sheaf attached to an `R`-module is extension of scalars from `R` to
the unique stalk ring of `RingedPoint.of R`.  Both directions of the comparison are concrete:
the forward map takes the germ of the top-open value, while the inverse descends the
extension-of-scalars unit through the neighborhood colimit defining the stalk.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
open scoped AlgebraicGeometry ChangeOfRings

noncomputable section

universe u

namespace AlgebraicGeometry.RingedPoint.Module

variable (R : Type u) [CommRing R]

/-- Extension of scalars from `R` to the unique stalk ring of `RingedPoint.of R`. -/
@[stacks 01BH "extension to the stalk ring of a ringed point"]
noncomputable abbrev stalkExtensionFunctor :
    ModuleCat.{u} R ⥤
      ModuleCat.{u} ((RingedPoint.of R).presheaf.stalk RingedPoint.point) :=
  ModuleCat.extendScalars (RingedPoint.stalkIso R).inv.hom

/-- Form the module sheaf on `RingedPoint.of R` and take its unique stalk. -/
@[stacks 01BH "stalk functor for modules on a ringed point"]
noncomputable abbrev stalkFunctor :
    ModuleCat.{u} R ⥤
      ModuleCat.{u} ((RingedPoint.of R).presheaf.stalk RingedPoint.point) :=
  RingedPoint.Module.functor R ⋙
    RingedSpace.stalkModuleFunctor (X := RingedPoint.of R) RingedPoint.point

/-- The germ at the unique point of the top-open value corresponding to `m`. -/
@[stacks 01BH "top-open germ for the point-module stalk comparison"]
noncomputable def stalkComparisonValue (M : ModuleCat.{u} R) (m : M) :
    RingedSpace.stalkModuleCat (RingedPoint.Module.sheaf R M) RingedPoint.point :=
  TopCat.Presheaf.Γgerm (RingedPoint.Module.sheaf R M).val.presheaf
      RingedPoint.point ((RingedPoint.Module.topValueIso R M).inv m)

/-- Taking the germ of the point-module top value preserves addition. -/
@[stacks 01BH "additivity of the point-module top-open germ"]
theorem stalkComparisonValue_add (M : ModuleCat.{u} R) (m n : M) :
    stalkComparisonValue R M (m + n) =
      stalkComparisonValue R M m + stalkComparisonValue R M n := sorry

/-- Taking the germ of the point-module top value is semilinear for the coefficient-to-stalk
map. -/
@[stacks 01BH "semilinearity of the point-module top-open germ"]
theorem stalkComparisonValue_smul (M : ModuleCat.{u} R) (r : R) (m : M) :
    stalkComparisonValue R M (r • m) =
      (RingedPoint.stalkIso R).inv r • stalkComparisonValue R M m := sorry

/-- The top-value germ map bundled as a semilinear map from `M` to the point-module stalk. -/
@[stacks 01BH "semilinear top-open germ map"]
noncomputable def stalkComparisonSemilinear (M : ModuleCat.{u} R) :
    (M : Type u) →ₛₗ[(RingedPoint.stalkIso R).inv.hom]
      (RingedSpace.stalkModuleCat (RingedPoint.Module.sheaf R M)
        RingedPoint.point : Type u) where
  toFun := stalkComparisonValue R M
  map_add' := stalkComparisonValue_add R M
  map_smul' := stalkComparisonValue_smul R M

/-- The top-value germ map regarded as a morphism into the scalar restriction of the stalk. -/
@[stacks 01BH "restricted top-open germ map"]
noncomputable def stalkComparisonRestricted (M : ModuleCat.{u} R) :
    M ⟶
      (ModuleCat.restrictScalars (RingedPoint.stalkIso R).inv.hom).obj
        (RingedSpace.stalkModuleCat (RingedPoint.Module.sheaf R M)
          RingedPoint.point) :=
  ModuleCat.semilinearMapAddEquiv (RingedPoint.stalkIso R).inv.hom M
    (RingedSpace.stalkModuleCat (RingedPoint.Module.sheaf R M)
      RingedPoint.point) (stalkComparisonSemilinear R M)

/-- The canonical map from scalar extension to the stalk of the corresponding point-module
sheaf. -/
@[stacks 01BH "point-module stalk comparison"]
noncomputable def stalkComparison (M : ModuleCat.{u} R) :
    (stalkExtensionFunctor R).obj M ⟶ (stalkFunctor R).obj M :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (RingedPoint.stalkIso R).inv.hom (stalkComparisonRestricted R M)

/-- The point-module stalk comparison sends `1 ⊗ₜ m` to the germ of the corresponding
top-open value. -/
@[stacks 01BH "point-module stalk comparison on pure tensors"]
theorem stalkComparison_one_tmul (M : ModuleCat.{u} R) (m : M) :
    stalkComparison R M
        ((1 : (RingedPoint.of R).presheaf.stalk RingedPoint.point) ⊗ₜ[
          R, (RingedPoint.stalkIso R).inv.hom] m) =
      stalkComparisonValue R M m := sorry

/-- The underlying additive map from the top-open value of a point-module sheaf back to its
coefficient module. -/
@[stacks 01BH "top-open module-value projection"]
noncomputable def stalkTopValueToModule (M : ModuleCat.{u} R) :
    (forget₂
      (ModuleCat.{u} ((RingedPoint.ringCatSheaf R).obj.obj
        (op (⊤ : Opens RingedPoint.carrier)))) AddCommGrpCat.{u}).obj
        ((RingedPoint.Module.sheaf R M).val.obj (op ⊤)) ⟶
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj M :=
  (forget₂
    (ModuleCat.{u} ((RingedPoint.ringCatSheaf R).obj.obj
      (op (⊤ : Opens RingedPoint.carrier)))) AddCommGrpCat.{u}).map
      (RingedPoint.Module.topValueIso R M).hom

/-- The additive map underlying the unit from a module to its scalar extension at the point
stalk. -/
@[stacks 01BH "extension-of-scalars unit at the point stalk"]
noncomputable def stalkExtensionUnit (M : ModuleCat.{u} R) :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj M ⟶
      (forget₂
        (ModuleCat.{u} ((RingedPoint.of R).presheaf.stalk RingedPoint.point))
          AddCommGrpCat.{u}).obj ((stalkExtensionFunctor R).obj M) :=
  (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
    ((ModuleCat.extendRestrictScalarsAdj
      (RingedPoint.stalkIso R).inv.hom).unit.app M)

/-- The top-open leg used to descend from the point-module stalk to scalar extension. -/
@[stacks 01BH "top-open inverse leg for the point-module stalk comparison"]
noncomputable def stalkComparisonInvTop (M : ModuleCat.{u} R) :
    (forget₂
      (ModuleCat.{u} ((RingedPoint.ringCatSheaf R).obj.obj
        (op (⊤ : Opens RingedPoint.carrier)))) AddCommGrpCat.{u}).obj
        ((RingedPoint.Module.sheaf R M).val.obj (op ⊤)) ⟶
      (forget₂
        (ModuleCat.{u} ((RingedPoint.of R).presheaf.stalk RingedPoint.point))
          AddCommGrpCat.{u}).obj ((stalkExtensionFunctor R).obj M) :=
  stalkTopValueToModule R M ≫ stalkExtensionUnit R M

/-- The neighborhood leg of the explicit inverse point-module stalk comparison. -/
@[stacks 01BH "neighborhood inverse leg for the point-module stalk comparison"]
noncomputable def stalkComparisonInvLeg (M : ModuleCat.{u} R)
    (U : (OpenNhds RingedPoint.point)ᵒᵖ) :
    (((OpenNhds.inclusion RingedPoint.point).op ⋙
      (RingedPoint.Module.sheaf R M).val.presheaf).obj U) ⟶
      (forget₂
        (ModuleCat.{u} ((RingedPoint.of R).presheaf.stalk RingedPoint.point))
          AddCommGrpCat.{u}).obj ((stalkExtensionFunctor R).obj M) :=
  eqToHom (congrArg
    (fun V ↦ (RingedPoint.Module.sheaf R M).val.presheaf.obj (op V))
    (pointOpen_eq_top U.unop.2)) ≫ stalkComparisonInvTop R M

/-- The neighborhood legs of the explicit inverse commute with restriction. -/
@[stacks 01BH "point-module inverse neighborhood naturality"]
theorem stalkComparisonInvLeg_naturality (M : ModuleCat.{u} R)
    {U V : (OpenNhds RingedPoint.point)ᵒᵖ} (i : U ⟶ V) :
    (((OpenNhds.inclusion RingedPoint.point).op ⋙
        (RingedPoint.Module.sheaf R M).val.presheaf).map i) ≫
        stalkComparisonInvLeg R M V =
      stalkComparisonInvLeg R M U := sorry

/-- The cocone whose descent map is the explicit inverse from the point-module stalk. -/
@[stacks 01BH "inverse cocone for the point-module stalk comparison"]
noncomputable def stalkComparisonInvCocone (M : ModuleCat.{u} R) :
    Cocone ((OpenNhds.inclusion RingedPoint.point).op ⋙
      (RingedPoint.Module.sheaf R M).val.presheaf) where
  pt := (forget₂
    (ModuleCat.{u} ((RingedPoint.of R).presheaf.stalk RingedPoint.point))
      AddCommGrpCat.{u}).obj ((stalkExtensionFunctor R).obj M)
  ι :=
    { app := stalkComparisonInvLeg R M
      naturality := fun _ _ i ↦ stalkComparisonInvLeg_naturality R M i }

/-- The additive map out of the stalk obtained by descending the explicit neighborhood
cocone. -/
@[stacks 01BH "additive inverse point-module stalk comparison"]
noncomputable def stalkComparisonInvAdd (M : ModuleCat.{u} R) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (RingedPoint.Module.sheaf R M).val.presheaf RingedPoint.point ⟶
      (forget₂
        (ModuleCat.{u} ((RingedPoint.of R).presheaf.stalk RingedPoint.point))
          AddCommGrpCat.{u}).obj ((stalkExtensionFunctor R).obj M) :=
  colimit.desc _ (stalkComparisonInvCocone R M)

/-- The descended additive inverse is linear over the point stalk ring. -/
@[stacks 01BH "linearity of the point-module stalk inverse"]
theorem stalkComparisonInvAdd_smul (M : ModuleCat.{u} R)
    (r : (RingedPoint.of R).presheaf.stalk RingedPoint.point)
    (m : RingedSpace.stalkModuleCat (RingedPoint.Module.sheaf R M)
      RingedPoint.point) :
    (stalkComparisonInvAdd R M (r • m) : (stalkExtensionFunctor R).obj M) =
      (((stalkExtensionFunctor R).obj M).smul r).hom
        (stalkComparisonInvAdd R M m) := sorry

/-- The explicit inverse from the point-module stalk to extension of scalars. -/
@[stacks 01BH "inverse point-module stalk comparison"]
noncomputable def stalkComparisonInv (M : ModuleCat.{u} R) :
    (stalkFunctor R).obj M ⟶ (stalkExtensionFunctor R).obj M :=
  ConcreteCategory.ofHom
    (C := ModuleCat.{u}
      ((RingedPoint.of R).presheaf.stalk RingedPoint.point))
    ({ toFun := fun m ↦
          (stalkComparisonInvAdd R M m : (stalkExtensionFunctor R).obj M)
       map_add' := (stalkComparisonInvAdd R M).hom.map_add
       map_smul' := stalkComparisonInvAdd_smul R M } :
      ((stalkFunctor R).obj M : Type u) →ₗ[
        (RingedPoint.of R).presheaf.stalk RingedPoint.point]
        ((stalkExtensionFunctor R).obj M : Type u))

/-- The point-module stalk comparison followed by its explicit inverse is the identity. -/
@[simp, stacks 01BH "point-module stalk comparison forward-inverse law"]
theorem stalkComparison_hom_inv_id (M : ModuleCat.{u} R) :
    stalkComparison R M ≫ stalkComparisonInv R M = 𝟙 _ := sorry

/-- The explicit inverse followed by the point-module stalk comparison is the identity. -/
@[simp, stacks 01BH "point-module stalk comparison inverse-forward law"]
theorem stalkComparison_inv_hom_id (M : ModuleCat.{u} R) :
    stalkComparisonInv R M ≫ stalkComparison R M = 𝟙 _ := sorry

/-- 01BH: An `R`-module extended to the unique point stalk is canonically isomorphic to the
stalk of its module sheaf on `RingedPoint.of R`. -/
@[stacks 01BH "module stalk on a ringed point"]
noncomputable def stalkModuleIso (M : ModuleCat.{u} R) :
    (stalkExtensionFunctor R).obj M ≅ (stalkFunctor R).obj M where
  hom := stalkComparison R M
  inv := stalkComparisonInv R M
  hom_inv_id := stalkComparison_hom_inv_id R M
  inv_hom_id := stalkComparison_inv_hom_id R M

/-- The canonical point-module stalk comparison is an isomorphism. -/
@[stacks 01BH "point-module stalk comparison is an isomorphism", instance]
noncomputable instance stalkComparison_isIso (M : ModuleCat.{u} R) :
    IsIso (stalkComparison R M) := sorry

/-- The point-module stalk comparison is natural in the coefficient module. -/
@[stacks 01BH "point-module stalk comparison naturality"]
theorem stalkComparison_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (stalkExtensionFunctor R).map f ≫ stalkComparison R N =
      stalkComparison R M ≫ (stalkFunctor R).map f := sorry

/-- The explicit inverse point-module stalk comparison is natural in the coefficient module. -/
@[stacks 01BH "point-module stalk inverse naturality"]
theorem stalkComparisonInv_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (stalkFunctor R).map f ≫ stalkComparisonInv R N =
      stalkComparisonInv R M ≫ (stalkExtensionFunctor R).map f := sorry

/-- The forward morphism of `stalkModuleIso` is the canonical germ comparison. -/
@[simp, stacks 01BH "point-module stalk isomorphism hom"]
theorem stalkModuleIso_hom (M : ModuleCat.{u} R) :
    (stalkModuleIso R M).hom = stalkComparison R M := sorry

/-- The inverse morphism of `stalkModuleIso` is the explicit neighborhood-colimit map. -/
@[simp, stacks 01BH "point-module stalk isomorphism inverse"]
theorem stalkModuleIso_inv (M : ModuleCat.{u} R) :
    (stalkModuleIso R M).inv = stalkComparisonInv R M := sorry

/-- The point-module stalk comparisons form a natural transformation. -/
@[stacks 01BH "point-module stalk natural transformation"]
noncomputable def stalkFunctorNatTrans :
    stalkExtensionFunctor R ⟶ stalkFunctor R where
  app M := stalkComparison R M
  naturality _ _ f := stalkComparison_naturality R f

/-- The inverse natural transformation for the point-module stalk comparison. -/
@[stacks 01BH "inverse point-module stalk natural transformation"]
noncomputable def stalkFunctorInvNatTrans :
    stalkFunctor R ⟶ stalkExtensionFunctor R where
  app M := stalkComparisonInv R M
  naturality _ _ f := stalkComparisonInv_naturality R f

/-- The forward point-module stalk transformation followed by its inverse is the identity. -/
@[simp, stacks 01BH "point-module stalk natural forward-inverse law"]
theorem stalkFunctorNatTrans_hom_inv_id :
    stalkFunctorNatTrans R ≫ stalkFunctorInvNatTrans R = 𝟙 _ := sorry

/-- The inverse point-module stalk transformation followed by the forward transformation is the
identity. -/
@[simp, stacks 01BH "point-module stalk natural inverse-forward law"]
theorem stalkFunctorNatTrans_inv_hom_id :
    stalkFunctorInvNatTrans R ≫ stalkFunctorNatTrans R = 𝟙 _ := sorry

/-- Extension to the unique stalk ring is naturally isomorphic to forming the point-module
sheaf and taking its stalk. -/
@[stacks 01BH "point-module stalk natural isomorphism"]
noncomputable def stalkFunctorIso :
    stalkExtensionFunctor R ≅ stalkFunctor R :=
  { hom := stalkFunctorNatTrans R
    inv := stalkFunctorInvNatTrans R
    hom_inv_id := stalkFunctorNatTrans_hom_inv_id R
    inv_hom_id := stalkFunctorNatTrans_inv_hom_id R }

/-- The forward natural transformation of `stalkFunctorIso` is the named comparison. -/
@[simp, stacks 01BH "point-module stalk natural isomorphism hom"]
theorem stalkFunctorIso_hom :
    (stalkFunctorIso R).hom = stalkFunctorNatTrans R := sorry

/-- The inverse natural transformation of `stalkFunctorIso` is the named inverse transformation. -/
@[simp, stacks 01BH "point-module stalk natural isomorphism inverse"]
theorem stalkFunctorIso_inv :
    (stalkFunctorIso R).inv = stalkFunctorInvNatTrans R := sorry

/-- A forward component of `stalkFunctorIso` is the point-module stalk comparison. -/
@[simp, stacks 01BH "point-module stalk natural isomorphism hom component"]
theorem stalkFunctorIso_hom_app (M : ModuleCat.{u} R) :
    (stalkFunctorIso R).hom.app M = stalkComparison R M := sorry

/-- An inverse component of `stalkFunctorIso` is the explicit point-module stalk inverse. -/
@[simp, stacks 01BH "point-module stalk natural isomorphism inverse component"]
theorem stalkFunctorIso_inv_app (M : ModuleCat.{u} R) :
    (stalkFunctorIso R).inv.app M = stalkComparisonInv R M := sorry

end AlgebraicGeometry.RingedPoint.Module
