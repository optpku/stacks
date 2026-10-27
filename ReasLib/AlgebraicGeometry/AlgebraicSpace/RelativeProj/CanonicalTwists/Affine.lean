/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.AffineModel
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.AffineStructureSheaf
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.CanonicalBaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections

/-! # Affine Serre models and their restrictions -/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace Opposite
open SheafOfModules.RingedSite

open scoped DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
variable {deg : DegreePieces 𝒜} (F : ProjFunctor X 𝒜)
variable (hF : F.IsAssociatedToQuadruples deg)

/-- The actual composite from an affine étale test of P to the base X. -/
def base (U : affineEtaleSite (toAlgebraicSpace F hF)) : ofOver U.obj.left ⟶ X :=
  U.obj.hom ≫ toAlgebraicSpace_hom F hF

/-- The genuine pullback algebra on the affine test scheme. -/
def localAlgebra (U : affineEtaleSite (toAlgebraicSpace F hF)) :
    GradedAlgebraSheaf.{u, u} U.obj.left.left.sheaf :=
  pullbackAlgebra (base F hF U) deg

/-- The affine pullback algebra is commutative. -/
instance localAlgebra_commutative (U : affineEtaleSite (toAlgebraicSpace F hF)) :
    (localAlgebra F hF U).IsCommutative := by
  -- Local instance justification (proof-local temporary data): commutativity comes from this explicit Proj owner F.
  letI := F.algebra_isCommutative
  exact pullbackAlgebra_isCommutative (base F hF U) deg

/-- The affine pullback algebra is quasi-coherent. -/
theorem localAlgebra_quasicoherent (U : affineEtaleSite (toAlgebraicSpace F hF)) :
    (localAlgebra F hF U).IsQuasicoherent :=
  pullbackAlgebra_isQuasicoherent (base F hF U) deg F.algebra_isQuasicoherent

/-- Evaluate the specified morphism U→P at the identity of U. -/
def functorPoint (U : affineEtaleSite (toAlgebraicSpace F hF)) :
    F.toFunctor.obj (op U.obj.left) :=
  (eqToIso (toAlgebraicSpace_functorOfPoints F hF)).hom.app (op U.obj.left)
    (U.obj.hom.app (op U.obj.left) (𝟙 U.obj.left))

/-- The existing classifying representative of that actual point. -/
def pointQuadruple (U : affineEtaleSite (toAlgebraicSpace F hF)) :
    Quadruple 𝒜 deg U.obj.left :=
  hF.quadrupleOf U.obj.left (functorPoint F hF U)

/-- Convert the representative by the actual QCoh site bridge over the identity of U. -/
def schemeQuadruple (U : affineEtaleSite (toAlgebraicSpace F hF)) :
    RelativeProjDegreeQuadruple (localAlgebra F hF U)
      (pointQuadruple F hF U).degree U.obj.left.left :=
  RelativeProjBaseChangeData.toSchemeQuadruple (T := U.obj.left)
    (base F hF U) deg F.algebra_isQuasicoherent (𝟙 U.obj.left)
    (pointQuadruple F hF U) sorry

/-- The affine classification map is pinned by the actual universal quadruple. -/
def classifyingChartMap (U : affineEtaleSite (toAlgebraicSpace F hF)) :
    U.obj.left.left ⟶
      Scheme.RelativeProjAffineSectionRing.chart (localAlgebra F hF U)
        (pointQuadruple F hF U).degree :=
  (Scheme.RelativeProjAffineSectionRing.degreeAssociated (localAlgebra F hF U)
    (localAlgebra_quasicoherent F hF U) (pointQuadruple F hF U).positive).pointOf
      U.obj.left.left (schemeQuadruple F hF U)

/-- The actual section of the section-algebra Proj attached to U→P. -/
def sectionMap (U : affineEtaleSite (toAlgebraicSpace F hF)) :
    U.obj.left.left ⟶ Scheme.RelativeProjAffineSectionRing.scheme (localAlgebra F hF U) :=
  classifyingChartMap F hF U ≫
    (Proj.degreeOpen (Scheme.RelativeProjAffineSectionRing.grading (localAlgebra F hF U))
      (pointQuadruple F hF U).degree).ι

/-- The classifying map lies over the identity of the affine test. -/
theorem sectionMap_toBase (U : affineEtaleSite (toAlgebraicSpace F hF)) :
    sectionMap F hF U ≫ Scheme.RelativeProjAffineSectionRing.toBase (localAlgebra F hF U) =
      𝟙 U.obj.left.left := sorry

/-- The actual local module in every integer degree. -/
def localObj (U : affineEtaleSite (toAlgebraicSpace F hF)) (n : ℤ) :
    U.obj.left.left.Modules :=
  (Scheme.Modules.pullback (sectionMap F hF U)).obj
    (Proj.AssociatedModule.twistingSheaf
      (Scheme.RelativeProjAffineSectionRing.grading (localAlgebra F hF U)) n)

/-- The actual local unit, transported by the specified pullback monoidal map. -/
def localUnit (U : affineEtaleSite (toAlgebraicSpace F hF)) :
    (𝟙_ U.obj.left.left.Modules) ⟶ localObj F hF U 0 :=
  (Scheme.Modules.pullbackUnitIso (sectionMap F hF U)).inv ≫
    (Scheme.Modules.pullback (sectionMap F hF U)).map
      (Proj.AssociatedModule.CanonicalAlgebra.oneHom
        (Scheme.RelativeProjAffineSectionRing.grading (localAlgebra F hF U)))

/-- The actual local multiplication; arbitrary twist multiplication is never supplied. -/
def localMul (U : affineEtaleSite (toAlgebraicSpace F hF)) (a b : ℤ) :
    localObj F hF U a ⊗ localObj F hF U b ⟶ localObj F hF U (a + b) :=
  (Scheme.Modules.pullbackTensorIso (sectionMap F hF U)
      (Proj.AssociatedModule.twistingSheaf
        (Scheme.RelativeProjAffineSectionRing.grading (localAlgebra F hF U)) a)
      (Proj.AssociatedModule.twistingSheaf
        (Scheme.RelativeProjAffineSectionRing.grading (localAlgebra F hF U)) b)).inv ≫
    (Scheme.Modules.pullback (sectionMap F hF U)).map
      (Proj.AssociatedModule.CanonicalAlgebra.mulHom
        (Scheme.RelativeProjAffineSectionRing.grading (localAlgebra F hF U)) a b)


variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
variable {deg : DegreePieces 𝒜} (F : ProjFunctor X 𝒜)
variable (hF : F.IsAssociatedToQuadruples deg)
variable {U V W : affineEtaleSite (toAlgebraicSpace F hF)}

/-- The defining triangle of an affine étale site morphism, composed with P→X. -/
theorem base_naturality (f : U ⟶ V) :
    ofOverMap f.hom.left ≫ base F hF V = base F hF U := sorry

/-- The degreewise comparison is the actual QCoh restriction/pullback comparison. -/
def localDegreePullIso (f : U ⟶ V) (n : ℕ) :
    (Scheme.Modules.pullback f.hom.left.left).obj (localAlgebra F hF V (n : ℤ)) ≅
      localAlgebra F hF U (n : ℤ) := by
  -- Local instance justification (proof-local temporary data): the explicit source owner supplies QCoh of degree n.
  letI := deg.isQuasicoherent F.algebra_isQuasicoherent n
  exact Modules.RestrictToScheme.compositePullbackIso (base F hF V) f.hom.left (deg.obj n) ≪≫
    (Modules.restrictToScheme U.obj.left).mapIso
      (eqToIso (congrArg (fun g ↦ (Modules.pullback g).obj (deg.obj n))
        (base_naturality F hF f)))

/-- Homogeneous global sections pull back along the actual scheme map. -/
def localDegreeSectionsMap (f : U ⟶ V) (n : ℕ) :
    RingedSpace.GradedAlgebraSections.degree (localAlgebra F hF V) n →+
      RingedSpace.GradedAlgebraSections.degree (localAlgebra F hF U) n :=
  (Scheme.Modules.globalSectionsMap (localDegreePullIso F hF f n).hom).hom.comp
    (Scheme.Modules.globalSectionsPullback f.hom.left.left
      (localAlgebra F hF V (n : ℤ))).hom

/-- Sum the actual homogeneous section maps into the actual direct-sum rings. -/
def localRingMap (f : U ⟶ V) :
    Scheme.RelativeProjAffineSectionRing.ring (localAlgebra F hF V) →+*
      Scheme.RelativeProjAffineSectionRing.ring (localAlgebra F hF U) :=
  DirectSum.toSemiring
    (fun n ↦ (DirectSum.of (RingedSpace.GradedAlgebraSections.degree (localAlgebra F hF U)) n).comp
      (localDegreeSectionsMap F hF f n)) sorry sorry

/-- The ring map preserves the displayed homogeneous summands. -/
def localGradedMap (f : U ⟶ V) :
    Scheme.RelativeProjAffineSectionRing.grading (localAlgebra F hF V) →+*ᵍ
      Scheme.RelativeProjAffineSectionRing.grading (localAlgebra F hF U) where
  toRingHom := localRingMap F hF f
  map_mem := sorry

/-- Affine QCoh pullback is scalar extension. Consequently this fixed graded
map has full projective domain, even for nonflat changes of the affine base. -/
theorem localGradedMap_domain (f : U ⟶ V) :
    projMapDomain (localGradedMap F hF f) = ⊤ := sorry

-- Local declaration justification (localized automation): the projective and fraction constructors use the already typed graded morphism; expanding its sectionwise Kan-extension implementation repeats geometric reduction without changing either constructor.
attribute [local irreducible] localGradedMap

set_option maxRecDepth 4096 in
/-- The actual projective map from the actual section-ring pullback. -/
def localProjMap (f : U ⟶ V) :
    Scheme.RelativeProjAffineSectionRing.scheme (localAlgebra F hF U) ⟶
      Scheme.RelativeProjAffineSectionRing.scheme (localAlgebra F hF V) :=
  Proj.AssociatedModule.GradedMap.fullMap.{u, u, u}
    (localGradedMap F hF f) (localGradedMap_domain F hF f)

/-- Both composites classify the pullback of the same universal quadruple. -/
theorem sectionMap_naturality (f : U ⟶ V) :
    sectionMap F hF U ≫ localProjMap F hF f = f.hom.left.left ≫ sectionMap F hF V := sorry

set_option maxRecDepth 4096 in
/-- The specific fraction-induced Serre comparison for this actual affine
pullback is invertible. This does not extend to arbitrary graded ring maps. -/
theorem localSerreMap_isIso (f : U ⟶ V) (n : ℤ) :
    IsIso (Proj.AssociatedModule.GradedMap.hom.{u, u, u}
      (localGradedMap F hF f) (localGradedMap_domain F hF f) n) := sorry

set_option maxRecDepth 4096 in
/-- Restrict the local twist along f by actual composite-pullback comparisons
and the actual fraction map, using only the true classifying-map square. -/
def localRestriction (f : U ⟶ V) (n : ℤ) :
    (Scheme.Modules.pullback f.hom.left.left).obj (localObj F hF V n) ⟶
      localObj F hF U n :=
  (Scheme.Modules.pullbackComp f.hom.left.left (sectionMap F hF V)).hom.app
      (Proj.AssociatedModule.twistingSheaf
        (Scheme.RelativeProjAffineSectionRing.grading (localAlgebra F hF V)) n) ≫
    eqToHom (congrArg (fun g ↦ (Scheme.Modules.pullback g).obj
      (Proj.AssociatedModule.twistingSheaf
        (Scheme.RelativeProjAffineSectionRing.grading (localAlgebra F hF V)) n))
      (sectionMap_naturality F hF f).symm) ≫
    (Scheme.Modules.pullbackComp (sectionMap F hF U) (localProjMap F hF f)).inv.app
      (Proj.AssociatedModule.twistingSheaf
        (Scheme.RelativeProjAffineSectionRing.grading (localAlgebra F hF V)) n) ≫
    (Scheme.Modules.pullback (sectionMap F hF U)).map
      (Proj.AssociatedModule.GradedMap.hom.{u, u, u}
        (localGradedMap F hF f) (localGradedMap_domain F hF f) n)

/-- Invertibility is attached to the specified transition morphism. -/
theorem localRestriction_isIso (f : U ⟶ V) (n : ℤ) :
    IsIso (localRestriction F hF f n) := sorry

/-- Restriction on actual top-open sections, used to form the affine-basis presheaf. -/
def localSectionsRestriction (f : U ⟶ V) (n : ℤ) :
    Scheme.Modules.globalSections (localObj F hF V n) ⟶
      Scheme.Modules.globalSections (localObj F hF U n) :=
  Scheme.Modules.globalSectionsPullback f.hom.left.left (localObj F hF V n) ≫
    Scheme.Modules.globalSectionsMap (localRestriction F hF f n)

end AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists
