module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.InverseImage
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.LowerShriek
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Underlying
public import ReasLib.Algebra.Category.Grp.Presheaf.Derived
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import ReasLib.CategoryTheory.Sites.Derived.InverseImage
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived underlying-sheaf comparison

The forgetful functor from module sheaves to additive sheaves is exact.  This leaf transports the
underived inverse-image square to derived categories and then takes its adjoint mate.  It is the
shared owner for derived lower-shriek/forgetful comparisons; geometric specializations only need
to prove that the resulting mate is invertible.
-/

@[expose] public section

-- Keep the existing standard derived-category model available in this leaf.
-- Local instance justification (defeq pin): the imported ModuleDerived and localized ModuleCat aliases use the standard homotopy localization; this fallback is definitionally the same quotient as the named moduleCat_hasDerivedCategory and does not choose another derived model.
attribute [local instance] HasDerivedCategory.standard

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe z uC vC uD vD w

namespace RingedSite.Hom

/-- The derived functor underlying a sheaf of modules on a ringed site. -/
@[stacks 07AE "derived underlying additive sheaf"]
noncomputable abbrev underlyingAbelianSheafDerived
    (X : RingedSite.{uC, vC, w})
    [UnivLE.{max uC vC, z}]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{z}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{z}]
    [HasSheafify X.siteTopology AddCommGrpCat.{z}] :
    ModuleDerived.{z} X ⥤
      DerivedCategory (Sheaf X.siteTopology AddCommGrpCat.{z}) :=
  (underlyingAbelianSheafExactFunctor.{z} X).mapDerivedCategory

/-- The exact-derived functor forgetting a module sheaf to its underlying additive presheaf.
The finite-colimit hypothesis is automatic for a chaotic topology. -/
@[stacks 08RX "derived underlying additive presheaf"]
noncomputable abbrev underlyingAbelianPresheafDerived
    (X : RingedSite.{uC, vC, w})
    [UnivLE.{max uC vC, z}]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{z}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{z}]
    [PreservesFiniteColimits
      (sheafToPresheaf X.siteTopology AddCommGrpCat.{z})] :
    ModuleDerived.{z} X ⥤
      DerivedCategory (AddCommGrpCat.Presheaf.{uC, vC, z} X) :=
  (underlyingAbelianPresheafExactFunctor.{z} X).mapDerivedCategory

end RingedSite.Hom

namespace RingedSite.Cocontinuous

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

variable (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
variable (R : Sheaf K RingCat.{w})
variable [UnivLE.{max uC vC, z}] [UnivLE.{max uD vD, z}]
variable [HasWeakSheafify J AddCommGrpCat.{z}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
variable [HasSheafify J AddCommGrpCat.{z}]
variable [HasWeakSheafify K AddCommGrpCat.{z}]
variable [K.WEqualsLocallyBijective AddCommGrpCat.{z}]
variable [HasSheafify K AddCommGrpCat.{z}]

namespace moduleInverseImage.derived

/-- The bundled exact square before passage to derived categories. -/
@[stacks 0798 "exact inverse-image underlying square"]
noncomputable def underivedIso :
    (moduleInverseImage.exactFunctor (J := J) (K := K) f R).comp
      (RingedSite.Hom.underlyingAbelianSheafExactFunctor
          (moduleInverseImage.source (J := J) (K := K) f R)) ≅
      (RingedSite.Hom.underlyingAbelianSheafExactFunctor
          (moduleInverseImage.target (K := K) R)).comp
        (siteAbelianInverseImageExact (C := C) (D := D) J K f) :=
  ObjectProperty.isoMk (CategoryTheory.exactFunctor _ _)
    (moduleInverseImage.underlyingIso (J := J) (K := K) f R)

/-- The derived inverse-image square obtained functorially from the exact underived square. -/
@[stacks 0798 "derived inverse-image underlying square"]
noncomputable def underlyingIso :
    (moduleInverseImage.derived (J := J) (K := K) f R) ⋙
        RingedSite.Hom.underlyingAbelianSheafDerived
          (moduleInverseImage.source (J := J) (K := K) f R) ≅
      RingedSite.Hom.underlyingAbelianSheafDerived
          (moduleInverseImage.target (K := K) R) ⋙
        siteAbelianInverseImageDerived (C := C) (D := D) J K f :=
  (ExactFunctor.MapDerivedCategory.compFunctorIso
      (moduleInverseImage.exactFunctor (J := J) (K := K) f R)
      (RingedSite.Hom.underlyingAbelianSheafExactFunctor
        (moduleInverseImage.source (J := J) (K := K) f R))).symm ≪≫
    ExactFunctor.MapDerivedCategory.mapIso (underivedIso f R) ≪≫
      ExactFunctor.MapDerivedCategory.compFunctorIso
        (RingedSite.Hom.underlyingAbelianSheafExactFunctor
          (moduleInverseImage.target (K := K) R))
        (siteAbelianInverseImageExact.{uC, vC, uD, vD} (C := C) (D := D) J K f)

end moduleInverseImage.derived

namespace moduleLowerShriek.derived

/-- The derived mate of the inverse-image/underlying square.  This is the canonical comparison
from abelian lower shriek followed by forgetting to module lower shriek followed by forgetting. -/
@[stacks 0798 "derived lower-shriek underlying comparison"]
noncomputable def underlyingComparison
    [Functor.IsRightAdjoint
        (siteAbelianInverseImageDerived (C := C) (D := D) J K f)] :
    RingedSite.Hom.underlyingAbelianSheafDerived
        (moduleInverseImage.source (J := J) (K := K) f R) ⋙
        Functor.leftAdjoint
          (siteAbelianInverseImageDerived (C := C) (D := D) J K f) ⟶
      moduleLowerShriek.derived (J := J) (K := K) f R ⋙
        RingedSite.Hom.underlyingAbelianSheafDerived
          (moduleInverseImage.target (K := K) R) :=
  CategoryTheory.DerivedBaseChange.mapOfRight
    (RingedSite.Cocontinuous.moduleLowerShriek.derived.adjunction
      (J := J) (K := K) f R)
    (Adjunction.ofIsRightAdjoint
      (siteAbelianInverseImageDerived (C := C) (D := D) J K f))
    (moduleInverseImage.derived.underlyingIso f R).hom

end moduleLowerShriek.derived

end RingedSite.Cocontinuous

end
