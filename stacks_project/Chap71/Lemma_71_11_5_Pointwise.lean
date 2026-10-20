module

public import stacks_project.Chap71.Lemma_71_11_5_BaseChange
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks

/-!
# The actual relative-Proj base-change morphism on points

On quasi-compact tests the maps transport genuine quadruples in the two
directions. On arbitrary tests they use the specified compatible systems over
quasi-compact opens. No compactness hypothesis is imposed on the test scheme
of the resulting natural isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

variable {S : Scheme.{u}} {X X' : AlgebraicSpace S} (g : X' ⟶ X)
variable {𝒜 𝒜'} {deg : DegreePieces 𝒜} {deg' : DegreePieces 𝒜'}
variable (hAlg : AlgebraPullback g deg deg')
variable {F : ProjFunctor X 𝒜} (hF : F.IsAssociatedToQuadruples deg)
variable {F' : ProjFunctor X' 𝒜'} (hF' : F'.IsAssociatedToQuadruples deg')

/-- On a quasi-compact test, push the representing quadruple along the base map. -/
def baseChangeForwardQc (T : Over S) [CompactSpace T.left]
    (x : F'.toFunctor.obj (op T)) : F.toFunctor.obj (op T) :=
  hF.pointOf T (hAlg.forwardQuadruple (hF'.quadrupleOf T x))

/-- On any test scheme, glue the actual images on quasi-compact opens. -/
def baseChangeForward (T : Over S) (x : F'.toFunctor.obj (op T)) :
    F.toFunctor.obj (op T) :=
  (hF.qcLimit T).symm
    (ProjFunctor.QcCompatibleSystem.of
      (fun V _ ↦ baseChangeForwardQc g hAlg hF hF' (openOver T V)
        (F'.toFunctor.map (op (openOverι T V)) x)) sorry)

/-- Pushalong of the classified quadruples defines a natural transformation. -/
def baseChangeForwardNat : F'.toFunctor ⟶ F.toFunctor where
  app T := TypeCat.ofHom (baseChangeForward g hAlg hF hF' T.unop)
  naturality := sorry

/-- The forward point map has the correct base point. -/
theorem baseChangeForwardNat_over :
    F'.baseMap ≫ g = baseChangeForwardNat g hAlg hF hF' ≫ F.baseMap := sorry

/-- The actual forward map into the sheaf fibre product is the categorical
pullback lift of the base point and transported quadruple class. -/
def canonicalBaseChangeHom : toAlgebraicSpace F' hF' ⟶ fibreProduct g hF :=
  pullback.lift F'.baseMap (baseChangeForwardNat g hAlg hF hF')
    (baseChangeForwardNat_over g hAlg hF hF')

/-- The base point of a fibre-product section lifts the structure map of its
represented quadruple, by the pullback equation and the association base law. -/
theorem inverseQuadruple_base (T : Over S) [CompactSpace T.left]
    (y : (fibreProduct g hF).functorOfPoints.obj (op T)) :
    pointHom ((fibreProduct_fst g hF).app (op T) y) ≫ g =
      (hF.quadrupleOf T ((fibreProduct_snd g hF).app (op T) y)).morphism := sorry

/-- The inverse point map on a quasi-compact test uses the actual inverse
transport of the homogeneous algebra maps. -/
def baseChangeInverseQc (T : Over S) [CompactSpace T.left]
    (y : (fibreProduct g hF).functorOfPoints.obj (op T)) : F'.toFunctor.obj (op T) :=
  hF'.pointOf T
    (hAlg.inverseQuadruple
      (pointHom ((fibreProduct_fst g hF).app (op T) y))
      (hF.quadrupleOf T ((fibreProduct_snd g hF).app (op T) y))
      (inverseQuadruple_base g hF T y))

/-- The inverse on arbitrary tests is assembled from the specified qc-open limit. -/
def baseChangeInverse (T : Over S)
    (y : (fibreProduct g hF).functorOfPoints.obj (op T)) : F'.toFunctor.obj (op T) :=
  (hF'.qcLimit T).symm
    (ProjFunctor.QcCompatibleSystem.of
      (fun V _ ↦ baseChangeInverseQc g hAlg hF hF' (openOver T V)
        ((fibreProduct g hF).functorOfPoints.map (op (openOverι T V)) y)) sorry)

/-- The actual inverse map is natural in the test scheme. -/
def canonicalBaseChangeInv : fibreProduct g hF ⟶ toAlgebraicSpace F' hF' where
  app T := TypeCat.ofHom (baseChangeInverse g hAlg hF hF' T.unop)
  naturality := sorry

/-- Quadruple pushalong followed by its inverse fixes the classified point. -/
theorem canonicalBaseChange_hom_inv_id :
    canonicalBaseChangeHom g hAlg hF hF' ≫ canonicalBaseChangeInv g hAlg hF hF' =
      𝟙 (toAlgebraicSpace F' hF') := sorry

/-- Inverse quadruple transport followed by pushalong fixes both fibre-product coordinates. -/
theorem canonicalBaseChange_inv_hom_id :
    canonicalBaseChangeInv g hAlg hF hF' ≫ canonicalBaseChangeHom g hAlg hF hF' =
      𝟙 (fibreProduct g hF) := sorry

/-- Relative-Proj base change with explicit mutually inverse point maps. -/
def canonicalBaseChangeIso : toAlgebraicSpace F' hF' ≅ fibreProduct g hF where
  hom := canonicalBaseChangeHom g hAlg hF hF'
  inv := canonicalBaseChangeInv g hAlg hF hF'
  hom_inv_id := canonicalBaseChange_hom_inv_id g hAlg hF hF'
  inv_hom_id := canonicalBaseChange_inv_hom_id g hAlg hF hF'

/-- The constructed isomorphism is over the changed base. -/
theorem canonicalBaseChangeIso_fst :
    (canonicalBaseChangeIso g hAlg hF hF').hom ≫ fibreProduct_fst g hF =
      toAlgebraicSpace_hom F' hF' := sorry

/-- The constructed isomorphism has precisely the source's forward and inverse
quadruple formulas, not an unspecified comparison action. -/
theorem canonicalBaseChangeIso_formula :
    ActsByStacksFormula g hAlg hF hF' (canonicalBaseChangeIso g hAlg hF hF') := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
