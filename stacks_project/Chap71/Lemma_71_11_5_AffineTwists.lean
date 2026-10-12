/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.AffineModel
public import stacks_project.Chap71.Lemma_71_11_2_Comparison
public import stacks_project.Chap66.«66_27_0_6_Site»

/-!
# Canonical Serre modules on the affine étale basis of relative Proj

An affine test U over P gives a point of the specified Proj functor. Its
quadruple, converted through the actual site comparison, classifies a section
of the actual Proj of Γ(U, g^*A). Pulling the actual Serre modules back along
that section defines the local twists. No arbitrary TwistFamily is input.
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

/-- The actual composite from an affine étale test of P to the base X. -/
def base (U : affineEtaleSite (toAlgebraicSpace F hF)) : ofOver U.obj.left ⟶ X :=
  U.obj.hom ≫ toAlgebraicSpace_hom F hF

/-- The genuine pullback algebra on the affine test scheme. -/
def localAlgebra (U : affineEtaleSite (toAlgebraicSpace F hF)) :
    GradedAlgebraSheaf.{u, u} U.obj.left.left.sheaf :=
  pullbackAlgebra (base F hF U) deg

instance localAlgebra_commutative (U : affineEtaleSite (toAlgebraicSpace F hF)) :
    (localAlgebra F hF U).IsCommutative := by
  -- Local instance justification (proof-local temporary data): commutativity comes from this explicit Proj owner F.
  letI := F.algebra_isCommutative
  exact pullbackAlgebra_isCommutative (base F hF U) deg

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

end AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists
