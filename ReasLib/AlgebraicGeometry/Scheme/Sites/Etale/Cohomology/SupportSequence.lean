/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.SupportTriangle
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open ComplexShape
open scoped ZeroObject

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.Support

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
variable (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})

/-- Homology of derived support is the closed direct image of the right-derived support functor. -/
def supportHomologyIso (degree : ℕ) :
    (DerivedCategory.homologyFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
      (degree : ℤ)).obj (derivedSupport i F) ≅
    (Abelian.directImage i).obj (((onClosed i).rightDerived degree).obj F) :=
  (DerivedCategory.homologyFunctorFactors _ (degree : ℤ)).app _ ≪≫
    (((onClosed i ⋙ Abelian.directImage i).mapHomologicalComplex (.up ℕ)).obj
      (injectiveResolution F).cocomplex).extendHomologyIso embeddingUpNat rfl ≪≫
    ((((onClosed i).mapHomologicalComplex (.up ℕ)).obj
      (injectiveResolution F).cocomplex).sc degree).mapHomologyIso (Abelian.directImage i) ≪≫
    (Abelian.directImage i).mapIso
      ((injectiveResolution F).isoRightDerivedObj (onClosed i) degree).symm

/-- Homology of the derived open image computes the higher direct images of the restricted sheaf. -/
def openHomologyIso (degree : ℕ) :
    (DerivedCategory.homologyFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
      (degree : ℤ)).obj (derivedOpen i F) ≅
    ((Abelian.directImage (closedImmersionComplement i).ι).rightDerived degree).obj
      ((Abelian.inverseImage (closedImmersionComplement i).ι).obj F) :=
  let resolution := injectiveResolution ((Abelian.inverseImage (closedImmersionComplement i).ι).obj F)
  let directImage := Abelian.directImage (closedImmersionComplement i).ι
  let mapped := (directImage.mapHomologicalComplex (.up ℕ)).obj resolution.cocomplex
  (DerivedCategory.homologyFunctorFactors _ (degree : ℤ)).app (mapped.extend embeddingUpNat) ≪≫
    mapped.extendHomologyIso embeddingUpNat rfl ≪≫
    (resolution.isoRightDerivedObj directImage degree).symm

/-- Degree-zero derived support is the closed direct image of sections with support. -/
def supportHomologyIsoZero :
    (DerivedCategory.homologyFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
      (derivedSupport i F) ≅ (Abelian.directImage i).obj ((onClosed i).obj F) :=
  supportHomologyIso i F 0 ≪≫
    (Abelian.directImage i).mapIso ((onClosed i).rightDerivedZeroIsoSelf.app F)

/-- Degree-zero derived open image is the ordinary direct image of the restricted sheaf. -/
def openHomologyIsoZero :
    (DerivedCategory.homologyFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
      (derivedOpen i F) ≅ (Abelian.directImage (closedImmersionComplement i).ι).obj
        ((Abelian.inverseImage (closedImmersionComplement i).ι).obj F) :=
  openHomologyIso i F 0 ≪≫
    (Abelian.directImage (closedImmersionComplement i).ι).rightDerivedZeroIsoSelf.app _

/-- The first support-sequence arrow is the degree-zero support map. -/
def sequenceSupportMap : (Abelian.directImage i).obj ((onClosed i).obj F) ⟶ F :=
  (supportHomologyIsoZero i F).inv ≫
    (DerivedCategory.homologyFunctor _ 0).map (supportMap i F) ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).hom.app F

/-- The restriction arrow in the support sequence is induced by the derived restriction unit. -/
def sequenceRestrictionMap : F ⟶
    (Abelian.directImage (closedImmersionComplement i).ι).obj
      ((Abelian.inverseImage (closedImmersionComplement i).ι).obj F) :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).inv.app F ≫
    (DerivedCategory.homologyFunctor _ 0).map (restrictionUnitMap i F) ≫
    (openHomologyIsoZero i F).hom

/-- The support-sequence connecting arrow is induced by the triangle boundary in degree zero. -/
def sequenceConnectingMap :
    (Abelian.directImage (closedImmersionComplement i).ι).obj
      ((Abelian.inverseImage (closedImmersionComplement i).ι).obj F) ⟶
    (Abelian.directImage i).obj (((onClosed i).rightDerived 1).obj F) :=
  (openHomologyIsoZero i F).inv ≫
    (DerivedCategory.homologyFunctor _ 0).map (boundaryMap i F) ≫
    ((DerivedCategory.homologyFunctor _ 0).shiftIso (1 : ℤ) 0 1 rfl).hom.app (derivedSupport i F) ≫
    (supportHomologyIso i F 1).hom

/-- The support sequence has zero endpoints and the supported, ambient, open-image, and first
support-cohomology sheaves as its four nonzero terms. -/
def sequence : ComposableArrows (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 5 :=
  ComposableArrows.mk₅
    (0 : 0 ⟶ (Abelian.directImage i).obj ((onClosed i).obj F))
    (sequenceSupportMap i F) (sequenceRestrictionMap i F) (sequenceConnectingMap i F)
    (0 : (Abelian.directImage i).obj (((onClosed i).rightDerived 1).obj F) ⟶ 0)

/-- The boundary induces an invertible homology map in each positive degree. -/
theorem boundaryHomology_isIso (degree : ℕ) (h_degree : 1 ≤ degree) :
    IsIso ((DerivedCategory.homologyFunctor _ (degree : ℤ)).map (boundaryMap i F)) := sorry

/-- The support sequence of a closed immersion is exact, including its zero endpoints. -/
theorem sequence_exact : (sequence i F).Exact := sorry

/-- Positive higher direct images from the complement are closed direct images of support
cohomology in the next degree. -/
def higherDirectImageIso (degree : ℕ) (h_degree : 1 ≤ degree) :
    ((Abelian.directImage (closedImmersionComplement i).ι).rightDerived degree).obj
      ((Abelian.inverseImage (closedImmersionComplement i).ι).obj F) ≅
    (Abelian.directImage i).obj (((onClosed i).rightDerived (degree + 1)).obj F) :=
  (openHomologyIso i F degree).symm ≪≫
    @asIso _ _ _ _ ((DerivedCategory.homologyFunctor _ (degree : ℤ)).map (boundaryMap i F))
      (boundaryHomology_isIso i F degree h_degree) ≪≫
    ((DerivedCategory.homologyFunctor _ 0).shiftIso 1 (degree : ℤ) ((degree + 1 : ℕ) : ℤ)
      ((Int.add_comm 1 (degree : ℤ)).trans (Int.natCast_add degree 1).symm)).app
      (derivedSupport i F) ≪≫
    supportHomologyIso i F (degree + 1)

end AlgebraicGeometry.Scheme.Etale.Support
