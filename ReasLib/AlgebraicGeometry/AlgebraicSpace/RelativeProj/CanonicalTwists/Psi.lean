/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists.Algebra
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.AffineSectionMap

/-!
# The canonical graded homomorphism `ψ : π^* 𝒜 ⟶ ⊕_{n ≥ 0} 𝒪_P(n)`

On each affine étale chart of `underline{Proj}_X(𝒜)`, the degree-`n` component is
the pullback of `homogeneousPullbackMap` along the classifying section. These
chart maps descend uniquely through restriction to the affine étale basis.
-/

@[expose] public section
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace SheafOfModules.RingedSite
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
variable {deg : DegreePieces 𝒜} (F : ProjFunctor X 𝒜)
variable (hF : F.IsAssociatedToQuadruples deg)

/-- Local `ψ` on an affine étale chart: pull back `homogeneousPullbackMap` of the
local section algebra along the classifying section. -/
def localPsi (U : affineEtaleSite (toAlgebraicSpace F hF)) (n : ℕ) :
    (Scheme.Modules.pullback (sectionMap F hF U)).obj
      ((Scheme.Modules.pullback
        (Scheme.RelativeProjAffineSectionRing.toBase (localAlgebra F hF U))).obj
        (localAlgebra F hF U (n : ℤ))) ⟶
    localObj F hF U n :=
  (Scheme.Modules.pullback (sectionMap F hF U)).map
    (Scheme.RelativeProjAffineSectionRing.homogeneousPullbackMap
      (localAlgebra F hF U) (localAlgebra_quasicoherent F hF U) n)

/-- Identify the iterated pullback of the local algebra along `sectionMap` and
`toBase` with the local algebra itself, using `sectionMap_toBase`. -/
def localPsiSourceIso (U : affineEtaleSite (toAlgebraicSpace F hF)) (n : ℕ) :
    (Scheme.Modules.pullback (sectionMap F hF U)).obj
      ((Scheme.Modules.pullback
        (Scheme.RelativeProjAffineSectionRing.toBase (localAlgebra F hF U))).obj
        (localAlgebra F hF U (n : ℤ))) ≅
    localAlgebra F hF U (n : ℤ) :=
  (Scheme.Modules.pullbackComp (sectionMap F hF U)
      (Scheme.RelativeProjAffineSectionRing.toBase (localAlgebra F hF U))).app
    (localAlgebra F hF U (n : ℤ)) ≪≫
  (Scheme.Modules.pullbackCongr (sectionMap_toBase F hF U)).app
    (localAlgebra F hF U (n : ℤ)) ≪≫
  (Scheme.Modules.pullbackId U.obj.left.left).app (localAlgebra F hF U (n : ℤ))

/-- The chartwise nonnegative twist map, as a morphism out of the local algebra. -/
def localPsiChart (U : affineEtaleSite (toAlgebraicSpace F hF)) (n : ℕ) :
    localAlgebra F hF U (n : ℤ) ⟶ localObj F hF U n :=
  (localPsiSourceIso F hF U n).inv ≫ localPsi F hF U n

/-- Identify the restricted pullback of `π^* 𝒜_n` with the local algebra, via
`pullbackCompIso` along `U.obj.hom ≫ π`. -/
def localAlgebraCompIso (U : affineEtaleSite (toAlgebraicSpace F hF)) (n : ℕ) :
    (Modules.restrictToScheme U.obj.left).obj
      ((Modules.pullback U.obj.hom).obj
        ((Modules.pullback (toAlgebraicSpace_hom F hF)).obj (deg.obj n))) ≅
    localAlgebra F hF U (n : ℤ) :=
  (Modules.restrictToScheme U.obj.left).mapIso
    ((Modules.pullbackCompIso U.obj.hom (toAlgebraicSpace_hom F hF)).app (deg.obj n))

/-- Top sections of the local algebra, with the affine-basis structure-ring action. -/
def affineSourceModule (U : affineEtaleSite (toAlgebraicSpace F hF)) (n : ℕ) :
    ModuleCat.{u} ((affineStructureSheaf (toAlgebraicSpace F hF)).obj.obj (op U)) :=
  (ModuleCat.restrictScalars
    (eqToIso (affineStructureSheaf_obj U)).hom.hom).obj
      (U.obj.left.left.toRingedSpace.moduleGlobalSectionsFunctor.obj
        (localAlgebra F hF U (n : ℤ)))

/-- Chartwise `localPsiChart` as a map of affine-basis modules. -/
def affinePsiApp (U : (affineEtaleSite (toAlgebraicSpace F hF))ᵒᵖ) (n : ℕ) :
    affineSourceModule F hF U.unop n ⟶ affineSectionModule F hF U.unop n :=
  @ModuleCat.ofHom
    ((affineStructureSheaf (toAlgebraicSpace F hF)).obj.obj U) _
    (affineSourceModule F hF U.unop n) (affineSectionModule F hF U.unop n)
    (affineSourceModule F hF U.unop n).isAddCommGroup
    (affineSourceModule F hF U.unop n).isModule
    (affineSectionModule F hF U.unop n).isAddCommGroup
    (affineSectionModule F hF U.unop n).isModule
    { toFun := (Scheme.Modules.globalSectionsMap (localPsiChart F hF U.unop n)).hom
      map_add' := sorry
      map_smul' := sorry }

/-- Restriction of `π^* 𝒜_n` to the affine étale basis. -/
def affinePullbackSheaf (n : ℕ) :
    SheafOfModules.{u} (affineStructureSheaf (toAlgebraicSpace F hF)) :=
  ((affineInclusionRingedHom (toAlgebraicSpace F hF)).modulePushforward).obj
    ((Modules.pullback (toAlgebraicSpace_hom F hF)).obj (deg.obj n))

/-- The identity-on-underlying-scheme comparison from the top-open étale object of an
affine chart to the chart itself. -/
def affineChartFromSiteObject
    (U : (affineEtaleSite (toAlgebraicSpace F hF))ᵒᵖ) :
    (Modules.restrictPostcompose U.unop.obj.hom).obj
      (Modules.RestrictToScheme.siteObject U.unop.obj.left ⊤) ⟶
    U.unop.obj :=
  MorphismProperty.CostructuredArrow.homMk
    (Over.homMk (⊤ : U.unop.obj.left.left.Opens).ι sorry) trivial sorry

/-- Sections of the affine-basis pullback sheaf are sections of `π^* 𝒜_n` on the
underlying small étale object. -/
def affinePullbackAsEtale
    (U : (affineEtaleSite (toAlgebraicSpace F hF))ᵒᵖ) (n : ℕ)
    (x : (affinePullbackSheaf F hF n).val.obj U) :
    ((Modules.pullback (toAlgebraicSpace_hom F hF)).obj (deg.obj n)).val.obj
      (op U.unop.obj) :=
  x

/-- Identify `π^* 𝒜_n` on an affine chart with the restricted composite pullback,
evaluated at the top open. -/
def affinePullbackToSourceApp (U : (affineEtaleSite (toAlgebraicSpace F hF))ᵒᵖ)
    (n : ℕ) :
    (affinePullbackSheaf F hF n).val.obj U ⟶
      (ModuleCat.restrictScalars
        (eqToIso (affineStructureSheaf_obj U.unop)).hom.hom).obj
          (((Modules.restrictToScheme U.unop.obj.left).obj
            ((Modules.pullback U.unop.obj.hom).obj
              ((Modules.pullback (toAlgebraicSpace_hom F hF)).obj
                (deg.obj n)))).val.obj (op ⊤)) :=
  @ModuleCat.ofHom
    ((affineStructureSheaf (toAlgebraicSpace F hF)).obj.obj U) _
    ((affinePullbackSheaf F hF n).val.obj U)
    ((ModuleCat.restrictScalars
      (eqToIso (affineStructureSheaf_obj U.unop)).hom.hom).obj
        (((Modules.restrictToScheme U.unop.obj.left).obj
          ((Modules.pullback U.unop.obj.hom).obj
            ((Modules.pullback (toAlgebraicSpace_hom F hF)).obj
              (deg.obj n)))).val.obj (op ⊤)))
    ((affinePullbackSheaf F hF n).val.obj U).isAddCommGroup
    ((affinePullbackSheaf F hF n).val.obj U).isModule
    ((ModuleCat.restrictScalars
      (eqToIso (affineStructureSheaf_obj U.unop)).hom.hom).obj
        (((Modules.restrictToScheme U.unop.obj.left).obj
          ((Modules.pullback U.unop.obj.hom).obj
            ((Modules.pullback (toAlgebraicSpace_hom F hF)).obj
              (deg.obj n)))).val.obj (op ⊤))).isAddCommGroup
    ((ModuleCat.restrictScalars
      (eqToIso (affineStructureSheaf_obj U.unop)).hom.hom).obj
        (((Modules.restrictToScheme U.unop.obj.left).obj
          ((Modules.pullback U.unop.obj.hom).obj
            ((Modules.pullback (toAlgebraicSpace_hom F hF)).obj
              (deg.obj n)))).val.obj (op ⊤))).isModule
    { toFun := fun x ↦
        (Modules.RestrictToScheme.sectionEquiv U.unop.obj.left
            ((Modules.pullback U.unop.obj.hom).obj
              ((Modules.pullback (toAlgebraicSpace_hom F hF)).obj (deg.obj n)))
            ⊤).symm
          (((@Modules.restrictFunctorIsoPullback _ _ _ U.unop.obj.hom
                (etale_hom U.unop.obj)).app
              ((Modules.pullback (toAlgebraicSpace_hom F hF)).obj (deg.obj n))).hom.val.app
            (op (Modules.RestrictToScheme.siteObject U.unop.obj.left ⊤))
            ((@Modules.restrictAppIso _ _ _
                ((Modules.pullback (toAlgebraicSpace_hom F hF)).obj (deg.obj n))
                U.unop.obj.hom (etale_hom U.unop.obj)
                (Modules.RestrictToScheme.siteObject U.unop.obj.left ⊤)).inv
              (((Modules.pullback (toAlgebraicSpace_hom F hF)).obj (deg.obj n)).val.map
                (affineChartFromSiteObject F hF U).op
                (affinePullbackAsEtale F hF U n x))))
      map_add' := sorry
      map_smul' := sorry }

/-- Transport restricted composite-pullback sections to local-algebra sections. -/
def restrictTopToLocalAlgebra (U : (affineEtaleSite (toAlgebraicSpace F hF))ᵒᵖ)
    (n : ℕ) :
    (ModuleCat.restrictScalars
        (eqToIso (affineStructureSheaf_obj U.unop)).hom.hom).obj
      (((Modules.restrictToScheme U.unop.obj.left).obj
        ((Modules.pullback U.unop.obj.hom).obj
          ((Modules.pullback (toAlgebraicSpace_hom F hF)).obj
            (deg.obj n)))).val.obj (op ⊤)) ⟶
      affineSourceModule F hF U.unop n :=
  (ModuleCat.restrictScalars
      (eqToIso (affineStructureSheaf_obj U.unop)).hom.hom).map
    ((localAlgebraCompIso F hF U.unop n).hom.val.app (op ⊤))

/-- Chartwise map from the restricted pullback `π^* 𝒜_n` to local Serre sections. -/
def affinePullbackPsiApp (U : (affineEtaleSite (toAlgebraicSpace F hF))ᵒᵖ) (n : ℕ) :
    (affinePullbackSheaf F hF n).val.obj U ⟶ affineSectionModule F hF U.unop n :=
  affinePullbackToSourceApp F hF U n ≫
    restrictTopToLocalAlgebra F hF U n ≫ affinePsiApp F hF U n

/-- The affine-basis morphism whose extension is the degree-`n` component of `ψ`. -/
def affinePullbackPsiMap (n : ℕ) :
    affinePullbackSheaf F hF n ⟶ affineSheaf F hF n where
  val :=
    { app := fun U ↦ affinePullbackPsiApp F hF U n
      naturality := sorry }

/-- The components of `affinePullbackPsiMap` are `affinePullbackPsiApp`. -/
theorem affinePullbackPsiMap_app (n : ℕ)
    (U : (affineEtaleSite (toAlgebraicSpace F hF))ᵒᵖ) :
    (affinePullbackPsiMap F hF n).val.app U = affinePullbackPsiApp F hF U n :=
  rfl


/-- Identify `π^* 𝒜_n` with its dense-basis extension. The forward map is the specified sectionwise inverse of the dense-basis counit. -/
def psiSourceIso (n : ℕ) :
    (Modules.pullback (toAlgebraicSpace_hom F hF)).obj (deg.obj n) ≅
      (affineExtension (toAlgebraicSpace F hF)).obj (affinePullbackSheaf F hF n) :=
  (affineExtensionCounitIso (toAlgebraicSpace F hF)
    ((Modules.pullback (toAlgebraicSpace_hom F hF)).obj (deg.obj n))).symm

/-- The degree-`n` component of `ψ`, obtained by descending `localPsiChart`. -/
def psiHom (n : ℕ) :
    (Modules.pullback (toAlgebraicSpace_hom F hF)).obj (deg.obj n) ⟶ obj F hF n :=
  (psiSourceIso F hF n).hom ≫
    (affineExtension (toAlgebraicSpace F hF)).map (affinePullbackPsiMap F hF n)

/-- A homomorphism of graded algebras `π^* 𝒜 ⟶ ⊕_{n ≥ 0} 𝒪_P(n)`, recorded
degreewise on nonnegative pieces together with the unit and multiplication laws. -/
structure CanonicalHom {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) where
  /-- The degree-`n` component `π^* 𝒜_n ⟶ 𝒪_P(n)`. -/
  hom : ∀ n : ℕ,
    (Modules.pullback (toAlgebraicSpace_hom F hF)).obj (deg.obj n) ⟶ obj F hF n
  /-- The degree-zero component preserves the unit. -/
  map_one :
    Modules.structureModulePullbackInv (toAlgebraicSpace_hom F hF) ≫
        (Modules.pullback (toAlgebraicSpace_hom F hF)).map (degreeZeroUnit deg) ≫
          hom 0 =
      unit F hF
  /-- Homogeneous components preserve multiplication. -/
  map_mul : ∀ i j : ℕ,
    pullbackTensorLax (toAlgebraicSpace_hom F hF) (deg.obj i) (deg.obj j) ≫
        (Modules.pullback (toAlgebraicSpace_hom F hF)).map (deg.mul i j) ≫
          hom (i + j) =
      tensorHom (hom i) (hom j) ≫
        mul F hF (Int.ofNat i) (Int.ofNat j) ≫
          eqToHom (congrArg (obj F hF) (Int.natCast_add i j))

namespace CanonicalHom

/-- Construct a canonical homomorphism from its degreewise components and laws. -/
def of {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {F : ProjFunctor X 𝒜}
    {hF : F.IsAssociatedToQuadruples deg}
    (hom : ∀ n : ℕ,
      (Modules.pullback (toAlgebraicSpace_hom F hF)).obj (deg.obj n) ⟶ obj F hF n)
    (map_one :
      Modules.structureModulePullbackInv (toAlgebraicSpace_hom F hF) ≫
          (Modules.pullback (toAlgebraicSpace_hom F hF)).map (degreeZeroUnit deg) ≫
            hom 0 =
        unit F hF)
    (map_mul : ∀ i j : ℕ,
      pullbackTensorLax (toAlgebraicSpace_hom F hF) (deg.obj i) (deg.obj j) ≫
          (Modules.pullback (toAlgebraicSpace_hom F hF)).map (deg.mul i j) ≫
            hom (i + j) =
        tensorHom (hom i) (hom j) ≫
          mul F hF (Int.ofNat i) (Int.ofNat j) ≫
            eqToHom (congrArg (obj F hF) (Int.natCast_add i j))) :
    CanonicalHom F hF where
  hom := hom
  map_one := map_one
  map_mul := map_mul

/-- The unit and multiplication laws of a canonical homomorphism. -/
def spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {F : ProjFunctor X 𝒜}
    {hF : F.IsAssociatedToQuadruples deg}
    (ψ : CanonicalHom F hF) : Prop :=
  (Modules.structureModulePullbackInv (toAlgebraicSpace_hom F hF) ≫
        (Modules.pullback (toAlgebraicSpace_hom F hF)).map (degreeZeroUnit deg) ≫
          ψ.hom 0 =
      unit F hF) ∧
    ∀ i j : ℕ,
      pullbackTensorLax (toAlgebraicSpace_hom F hF) (deg.obj i) (deg.obj j) ≫
          (Modules.pullback (toAlgebraicSpace_hom F hF)).map (deg.mul i j) ≫
            ψ.hom (i + j) =
        tensorHom (ψ.hom i) (ψ.hom j) ≫
          mul F hF (Int.ofNat i) (Int.ofNat j) ≫
            eqToHom (congrArg (obj F hF) (Int.natCast_add i j))

/-- Every canonical homomorphism satisfies `spec`. -/
theorem spec_of {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {F : ProjFunctor X 𝒜}
    {hF : F.IsAssociatedToQuadruples deg}
    (ψ : CanonicalHom F hF) : spec ψ :=
  ⟨ψ.map_one, ψ.map_mul⟩

end CanonicalHom

/-- The canonical homomorphism `ψ : π^* 𝒜 ⟶ ⊕_{n ≥ 0} 𝒪_P(n)`. -/
def psi : CanonicalHom F hF where
  hom := psiHom F hF
  map_one := sorry
  map_mul := sorry

/-- The degree-`n` component of `psi` is `psiHom`. -/
theorem psi_hom (n : ℕ) : (psi F hF).hom n = psiHom F hF n :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists
