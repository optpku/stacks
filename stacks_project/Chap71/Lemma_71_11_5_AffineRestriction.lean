/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap71.Lemma_71_11_5_AffineTwists
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.CanonicalBaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections

/-!
# Actual transition maps for canonical affine étale Serre models

The graded ring map is the direct sum of pullback on homogeneous sections,
followed by the specified QCoh site-composition comparison. The module map is
the actual homogeneous fraction map, pulled back along the classifying section.
-/

@[expose] public section
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace SheafOfModules.RingedSite
open scoped DirectSum
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists

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
instance localRestriction_isIso (f : U ⟶ V) (n : ℤ) :
    IsIso (localRestriction F hF f n) := sorry

/-- Restriction on actual top-open sections, used to form the affine-basis presheaf. -/
def localSectionsRestriction (f : U ⟶ V) (n : ℤ) :
    Scheme.Modules.globalSections (localObj F hF V n) ⟶
      Scheme.Modules.globalSections (localObj F hF U n) :=
  Scheme.Modules.globalSectionsPullback f.hom.left.left (localObj F hF V n) ≫
    Scheme.Modules.globalSectionsMap (localRestriction F hF f n)

end AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists
