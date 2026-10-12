/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.LowerShriek
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Underlying
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition

/-!
# Derived lower shriek for inherited sites

This file derives the module and abelian inverse-image functors attached to a
morphism of fibred categories, names their left adjoints, and exposes the
canonical mate comparing the two lower-shriek functors after forgetting
module structure.
-/

@[expose] public section

open CategoryTheory
open RingedSite.Hom

noncomputable section

universe u v

namespace CategoryTheory.FiberedCategoryOver.DerivedLowerShriek

variable {D : RingedSite.{u, v}}
variable {C C' : FiberedCategoryOver.{u, v, u, v} D.carrier}

section Exact

variable (f : C' ⟶ C)
variable [IsMorphismOfSites
  (C'.p.inheritedTopology D.siteTopology)
  (C.p.inheritedTopology D.siteTopology)
  (FiberedCategoryOver.toFunctor f)]
variable [Functor.IsCocontinuous
  (FiberedCategoryOver.toFunctor f)
  (sourceTopology D C') (sourceTopology D C)]

/-- Lemma 21.38.5 (08PC), derived part: module inverse image for a morphism of fibred
categories is exact. -/
@[stacks 08PC "(3) exact module inverse image"]
theorem moduleInverseImage_exact :
    exactFunctor
      (RingedSite.ModuleCat.{max u v} C.p.inheritedRingedSite)
      (RingedSite.ModuleCat.{max u v} C'.p.inheritedRingedSite)
      (FiberedCategoryOver.moduleInverseImage f) := sorry

/-- The module inverse image bundled with its exactness certificate. -/
@[stacks 08PC "(3) bundled exact module inverse image"]
noncomputable def moduleInverseImageExact :
    RingedSite.ModuleCat.{max u v} C.p.inheritedRingedSite ⥤ₑ
      RingedSite.ModuleCat.{max u v} C'.p.inheritedRingedSite :=
  ⟨FiberedCategoryOver.moduleInverseImage f, moduleInverseImage_exact f⟩

/-- The abelian inverse image bundled with the canonical exactness certificate. -/
@[stacks 08PC "(3) bundled exact abelian inverse image"]
noncomputable abbrev abelianInverseImageExact :
    Sheaf (sourceTopology D C) AddCommGrpCat.{max u v} ⥤ₑ
      Sheaf (sourceTopology D C') AddCommGrpCat.{max u v} :=
  siteAbelianInverseImageExact (sourceTopology D C')
    (sourceTopology D C) (FiberedCategoryOver.toFunctor f)

end Exact

section Derived

variable (f : C' ⟶ C)
variable [IsMorphismOfSites
  (C'.p.inheritedTopology D.siteTopology)
  (C.p.inheritedTopology D.siteTopology)
  (FiberedCategoryOver.toFunctor f)]
variable [Functor.IsCocontinuous
  (FiberedCategoryOver.toFunctor f)
  (sourceTopology D C') (sourceTopology D C)]
variable [UnivLE.{max u v, max u v}]

/-- The exact derived module inverse image for a morphism of fibred categories. -/
@[stacks 08PC "(3) derived module inverse image"]
noncomputable abbrev moduleInverseImage :
    ModuleDerived.{max u v} C.p.inheritedRingedSite ⥤
      ModuleDerived.{max u v} C'.p.inheritedRingedSite :=
  (moduleInverseImageExact f).mapDerivedCategory

/-- The exact derived abelian inverse image for a morphism of fibred categories. -/
@[stacks 08PC "(3) derived abelian inverse image"]
noncomputable abbrev abelianInverseImage :
    DerivedCategory (Sheaf (sourceTopology D C) AddCommGrpCat.{max u v}) ⥤
      DerivedCategory (Sheaf (sourceTopology D C') AddCommGrpCat.{max u v}) :=
  (abelianInverseImageExact f).mapDerivedCategory

namespace moduleInverseImage

/-- Lemma 21.38.5 (08PC), derived part: derived module inverse image admits a left adjoint. -/
@[stacks 08PC "(3) derived module lower-shriek existence", instance]
theorem isRightAdjoint : Functor.IsRightAdjoint (moduleInverseImage f) := sorry

end moduleInverseImage

namespace abelianInverseImage

/-- Lemma 21.38.5 (08PC), derived part: derived abelian inverse image admits a left adjoint. -/
@[stacks 08PC "(3) derived abelian lower-shriek existence", instance]
theorem isRightAdjoint : Functor.IsRightAdjoint (abelianInverseImage f) := sorry

end abelianInverseImage

/-- The derived lower-shriek functor on module sheaves. -/
@[stacks 08PC "(3) derived module lower shriek"]
noncomputable abbrev moduleLowerShriek :
    ModuleDerived.{max u v} C'.p.inheritedRingedSite ⥤
      ModuleDerived.{max u v} C.p.inheritedRingedSite :=
  Functor.leftAdjoint (moduleInverseImage f)

/-- The adjunction characterizing derived module lower shriek. -/
@[stacks 08PC "(3) derived module lower-shriek adjunction"]
noncomputable def moduleAdjunction : moduleLowerShriek f ⊣ moduleInverseImage f :=
  Adjunction.ofIsRightAdjoint (moduleInverseImage f)

/-- The derived lower-shriek functor on abelian sheaves. -/
@[stacks 08PC "(3) derived abelian lower shriek"]
noncomputable abbrev abelianLowerShriek :
    DerivedCategory (Sheaf (sourceTopology D C') AddCommGrpCat.{max u v}) ⥤
      DerivedCategory (Sheaf (sourceTopology D C) AddCommGrpCat.{max u v}) :=
  Functor.leftAdjoint (abelianInverseImage f)

/-- The adjunction characterizing derived abelian lower shriek. -/
@[stacks 08PC "(3) derived abelian lower-shriek adjunction"]
noncomputable def abelianAdjunction : abelianLowerShriek f ⊣ abelianInverseImage f :=
  Adjunction.ofIsRightAdjoint (abelianInverseImage f)

end Derived

section Comparison

variable (f : C' ⟶ C)
variable [IsMorphismOfSites
  (C'.p.inheritedTopology D.siteTopology)
  (C.p.inheritedTopology D.siteTopology)
  (FiberedCategoryOver.toFunctor f)]
variable [Functor.IsCocontinuous
  (FiberedCategoryOver.toFunctor f)
  (sourceTopology D C') (sourceTopology D C)]
variable [UnivLE.{max u v, max u v}]
variable [HasWeakSheafify (sourceTopology D C') AddCommGrpCat.{max u v}]
variable [(sourceTopology D C').WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasSheafify (sourceTopology D C') AddCommGrpCat.{max u v}]
variable [HasWeakSheafify (sourceTopology D C) AddCommGrpCat.{max u v}]
variable [(sourceTopology D C).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasSheafify (sourceTopology D C) AddCommGrpCat.{max u v}]

/-- The underived exact square expressing compatibility of inverse image with forgetting module
structure.  Its underlying natural isomorphism is definitionally the identity. -/
@[stacks 08PC "(4) exact inverse-image forgetful square"]
noncomputable def underivedUnderlyingIso :
    (moduleInverseImageExact f).comp
        (underlyingAbelianSheafExactFunctor C'.p.inheritedRingedSite) ≅
      (underlyingAbelianSheafExactFunctor C.p.inheritedRingedSite).comp
        (abelianInverseImageExact f) :=
  ObjectProperty.isoMk _ (Iso.refl _)

/-- The derived inverse-image square obtained from the underived exact square. -/
@[stacks 08PC "(4) derived inverse-image forgetful square"]
noncomputable def underlyingIso :
    moduleInverseImage f ⋙ underlyingAbelianSheafDerived C'.p.inheritedRingedSite ≅
      underlyingAbelianSheafDerived C.p.inheritedRingedSite ⋙ abelianInverseImage f :=
  (ExactFunctor.MapDerivedCategory.compFunctorIso
      (moduleInverseImageExact f)
      (underlyingAbelianSheafExactFunctor C'.p.inheritedRingedSite)).symm ≪≫
    ExactFunctor.MapDerivedCategory.mapIso (underivedUnderlyingIso f) ≪≫
      ExactFunctor.MapDerivedCategory.compFunctorIso
        (underlyingAbelianSheafExactFunctor C.p.inheritedRingedSite)
        (abelianInverseImageExact f)

/-- Lemma 21.38.5 (08PC), derived part: the canonical mate comparing derived abelian and module
lower shriek after forgetting module structure. -/
@[stacks 08PC "(4) derived lower-shriek forgetful comparison"]
noncomputable def underlyingComparison :
    underlyingAbelianSheafDerived C'.p.inheritedRingedSite ⋙ abelianLowerShriek f ⟶
      moduleLowerShriek f ⋙ underlyingAbelianSheafDerived C.p.inheritedRingedSite :=
  CategoryTheory.DerivedBaseChange.mapOfRight
    (moduleAdjunction f) (abelianAdjunction f) (underlyingIso f).hom

/-- Lemma 21.38.5 (08PC), derived part: the lower-shriek/forgetful comparison is invertible. -/
@[stacks 08PC "(4) commutation with the derived forgetful functor", instance]
theorem underlyingComparison_isIso : IsIso (underlyingComparison f) := sorry

end Comparison

-- The exact functor stores only `moduleInverseImage_exact`, a Prop-valued proof.  The inverse-image
-- functor, the identity square, and the derived mate are explicit canonical data.

end CategoryTheory.FiberedCategoryOver.DerivedLowerShriek
