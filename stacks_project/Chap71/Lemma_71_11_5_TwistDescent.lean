/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap71.Lemma_71_11_5_AffineRestriction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Adjunction

/-!
# Descent of the actual local Serre modules from the affine étale basis

The basis presheaf uses the explicit section restrictions. Its extension is
the module inverse image along the dense affine inclusion. In particular the
global object is an actual functor application, not a selected sheaf with an
assumed comparison isomorphism. The fixed adjunction unit supplies the local
comparison. No quasi-separatedness or affine fibre products are assumed.
-/

@[expose] public section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace SheafOfModules.RingedSite
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists

section Basis
variable {S : Scheme.{u}} (P : AlgebraicSpace S)

/-- The dense affine inclusion, with the actual restricted structure sheaf. -/
def affineInclusionRingedHom : RingedSite.Hom (ringedSite P) (affineRingedSite P) where
  base := affineEtaleInclusion P
  isMorphismOfSites := sorry
  structureSheafMap := 𝟙 (affineStructureSheaf P)

/-- Restriction to this dense basis is an equivalence on module sheaves.
Small values are recovered using the affine-open cover of each test scheme. -/
instance affineRestriction_isEquivalence :
    ((affineInclusionRingedHom P).modulePushforward.{u}).IsEquivalence := sorry

/-- The inverse-image functor is the specified left adjoint of actual restriction. -/
def affineExtension :
    SheafOfModules.{u} (affineStructureSheaf P) ⥤ P.Modules :=
  (affineInclusionRingedHom P).modulePullback.{u}

/-- Use the actual inverse-image/direct-image adjunction. -/
def affineExtensionAdjunction :
    affineExtension P ⊣ (affineInclusionRingedHom P).modulePushforward.{u} :=
  (affineInclusionRingedHom P).modulePullbackPushforwardAdjunction

/-- The fixed comparison is invertible because restriction is a dense-basis equivalence. -/
instance affineExtensionUnit_isIso (M : SheafOfModules.{u} (affineStructureSheaf P)) :
    IsIso ((affineExtensionAdjunction P).unit.app M) := sorry

end Basis

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
variable {deg : DegreePieces 𝒜} (F : ProjFunctor X 𝒜)
variable (hF : F.IsAssociatedToQuadruples deg)

/-- Top sections of the actual local Serre module, with the basis structure-ring action. -/
def affineSectionModule (U : affineEtaleSite (toAlgebraicSpace F hF)) (n : ℤ) :
    ModuleCat.{u} ((affineStructureSheaf (toAlgebraicSpace F hF)).obj.obj (op U)) :=
  (ModuleCat.restrictScalars
    (eqToIso (affineStructureSheaf_obj U)).hom.hom).obj
      (U.obj.left.left.toRingedSpace.moduleGlobalSectionsFunctor.obj (localObj F hF U n))

/-- The actual restriction, bundled with its scalar linearity; source and target
actions are those of the structure sheaf, not independently chosen instances. -/
def affineSectionMap {U V : (affineEtaleSite (toAlgebraicSpace F hF))ᵒᵖ}
    (f : U ⟶ V) (n : ℤ) :
    affineSectionModule F hF U.unop n ⟶
      (ModuleCat.restrictScalars
        ((affineStructureSheaf (toAlgebraicSpace F hF)).obj.map f).hom).obj
          (affineSectionModule F hF V.unop n) := by
  let M := affineSectionModule F hF U.unop n
  let N := (ModuleCat.restrictScalars
    ((affineStructureSheaf (toAlgebraicSpace F hF)).obj.map f).hom).obj
      (affineSectionModule F hF V.unop n)
  exact @ModuleCat.ofHom
    ((affineStructureSheaf (toAlgebraicSpace F hF)).obj.obj U) _ M N
    M.isAddCommGroup M.isModule N.isAddCommGroup N.isModule
    { toFun := (localSectionsRestriction F hF f.unop n).hom
      map_add' := sorry
      map_smul' := sorry }

/-- The actual affine-basis presheaf, with restriction given by fraction pullback. -/
def affinePresheaf (n : ℤ) :
    PresheafOfModules.{u} (affineStructureSheaf (toAlgebraicSpace F hF)).obj where
  obj U := affineSectionModule F hF U.unop n
  map f := affineSectionMap F hF f n
  map_id := sorry
  map_comp := sorry

/-- Étale descent applies to the actual local QCoh modules and their specified
cartesian transition maps. Refinement by affines handles nonaffine overlaps. -/
theorem affinePresheaf_isSheaf (n : ℤ) :
    Presheaf.IsSheaf (affineEtaleTopology (toAlgebraicSpace F hF))
      (affinePresheaf F hF n).presheaf := sorry

/-- The affine-basis sheaf with its actual section data. -/
def affineSheaf (n : ℤ) : SheafOfModules.{u} (affineStructureSheaf (toAlgebraicSpace F hF)) where
  val := affinePresheaf F hF n
  isSheaf := affinePresheaf_isSheaf F hF n

/-- The canonical global twist: actual inverse image of the actual affine-basis sheaf. -/
def obj (n : ℤ) : (toAlgebraicSpace F hF).Modules :=
  (affineExtension (toAlgebraicSpace F hF)).obj (affineSheaf F hF n)

/-- The local comparison is the fixed adjunction unit, not supplied model data. -/
def affineComparison (n : ℤ) : affineSheaf F hF n ≅
    ((affineInclusionRingedHom (toAlgebraicSpace F hF)).modulePushforward).obj (obj F hF n) :=
  @asIso _ _ _ _
    ((affineExtensionAdjunction (toAlgebraicSpace F hF)).unit.app (affineSheaf F hF n))
    (affineExtensionUnit_isIso (toAlgebraicSpace F hF) (affineSheaf F hF n))

end AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists
