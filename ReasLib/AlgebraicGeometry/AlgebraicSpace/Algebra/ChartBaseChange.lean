module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.Chart
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Logic.Function.Basic

/-!
# Actual quasi-coherent algebra base change on affine étale charts

The canonical commutative-ring pushout records the scalar extension of the
algebra's actual section map. Quasi-coherence identifies this pushout with the
sections on an affine source chart. The inverse function searches the fibers
of that fixed map; its data do not take a bijectivity proof as an input.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Scalar extension of the specified section algebra along the actual scheme-chart map. -/
def sectionBaseChangeRing (A : X.QcAlgebraUnder) {U V : smallEtaleSite X} (m : U ⟶ V) :
    CommRingCat.{u} :=
  pushout (structureMap A V) m.left.left.appTop

/-- The original section-algebra maps commute with the chart's structural ring map. -/
theorem sectionBaseChange_w (A : X.QcAlgebraUnder) {U V : smallEtaleSite X} (m : U ⟶ V) :
    structureMap A V ≫ A.obj.right.obj.map m.op =
      m.left.left.appTop ≫ structureMap A U := sorry

/-- The canonical map from scalar-extended sections to the sections on the source chart. -/
def sectionBaseChangeMap (A : X.QcAlgebraUnder) {U V : smallEtaleSite X} (m : U ⟶ V) :
    sectionBaseChangeRing A m ⟶ sectionRing A U :=
  pushout.desc (A.obj.right.obj.map m.op) (structureMap A U) (sectionBaseChange_w A m)

/-- On affine étale charts the canonical scalar-extension map is bijective by quasi-coherence. -/
theorem sectionBaseChangeMap_bijective (A : X.QcAlgebraUnder) {U V : smallEtaleSite X}
    [IsAffine U.left.left] [IsAffine V.left.left] (m : U ⟶ V) :
    Function.Bijective (sectionBaseChangeMap A m).hom := sorry

/-- The inverse section function is the actual fiber inverse of the specified scalar-extension map.
Zero only supplies the total function's default; the affine bijectivity law fixes every value. -/
def sectionBaseChangeInverseApply (A : X.QcAlgebraUnder) {U V : smallEtaleSite X} (m : U ⟶ V) :
    sectionRing A U → sectionBaseChangeRing A m :=
  @Function.invFun (sectionBaseChangeRing A m) (sectionRing A U) ⟨0⟩
    (sectionBaseChangeMap A m).hom

/-- Applying the canonical map to an inverse section recovers the original section. -/
theorem sectionBaseChangeMap_inverseApply (A : X.QcAlgebraUnder) {U V : smallEtaleSite X}
    [IsAffine U.left.left] [IsAffine V.left.left] (m : U ⟶ V) (a : sectionRing A U) :
    (sectionBaseChangeMap A m).hom (sectionBaseChangeInverseApply A m a) = a := sorry

/-- The inverse section function recovers every scalar-extended section. -/
theorem sectionBaseChangeInverseApply_map (A : X.QcAlgebraUnder) {U V : smallEtaleSite X}
    [IsAffine U.left.left] [IsAffine V.left.left] (m : U ⟶ V) (a : sectionBaseChangeRing A m) :
    sectionBaseChangeInverseApply A m ((sectionBaseChangeMap A m).hom a) = a := sorry

/-- The selected preimage is uniquely determined by its specified image. -/
theorem sectionBaseChangeInverseApply_eq_iff (A : X.QcAlgebraUnder) {U V : smallEtaleSite X}
    [IsAffine U.left.left] [IsAffine V.left.left] (m : U ⟶ V)
    (a : sectionRing A U) (b : sectionBaseChangeRing A m) :
    sectionBaseChangeInverseApply A m a = b ↔ (sectionBaseChangeMap A m).hom b = a := sorry

/-- The affine scalar-extension inverse preserves the unit section. -/
theorem sectionBaseChangeInverseApply_one (A : X.QcAlgebraUnder) {U V : smallEtaleSite X}
    [IsAffine U.left.left] [IsAffine V.left.left] (m : U ⟶ V) :
    sectionBaseChangeInverseApply A m 1 = 1 := sorry

/-- The affine scalar-extension inverse preserves products of sections. -/
theorem sectionBaseChangeInverseApply_mul (A : X.QcAlgebraUnder) {U V : smallEtaleSite X}
    [IsAffine U.left.left] [IsAffine V.left.left] (m : U ⟶ V) (a b : sectionRing A U) :
    sectionBaseChangeInverseApply A m (a * b) =
      sectionBaseChangeInverseApply A m a * sectionBaseChangeInverseApply A m b := sorry

/-- The affine scalar-extension inverse preserves the zero section. -/
theorem sectionBaseChangeInverseApply_zero (A : X.QcAlgebraUnder) {U V : smallEtaleSite X}
    [IsAffine U.left.left] [IsAffine V.left.left] (m : U ⟶ V) :
    sectionBaseChangeInverseApply A m 0 = 0 := sorry

/-- The affine scalar-extension inverse preserves sums of sections. -/
theorem sectionBaseChangeInverseApply_add (A : X.QcAlgebraUnder) {U V : smallEtaleSite X}
    [IsAffine U.left.left] [IsAffine V.left.left] (m : U ⟶ V) (a b : sectionRing A U) :
    sectionBaseChangeInverseApply A m (a + b) =
      sectionBaseChangeInverseApply A m a + sectionBaseChangeInverseApply A m b := sorry

/-- The affine quasi-coherent inverse has this actual section function as its ring map. -/
def sectionBaseChangeInverse (A : X.QcAlgebraUnder) {U V : smallEtaleSite X}
    [IsAffine U.left.left] [IsAffine V.left.left] (m : U ⟶ V) :
    sectionRing A U ⟶ sectionBaseChangeRing A m :=
  CommRingCat.ofHom
    { toFun := sectionBaseChangeInverseApply A m
      map_one' := sectionBaseChangeInverseApply_one A m
      map_mul' := sectionBaseChangeInverseApply_mul A m
      map_zero' := sectionBaseChangeInverseApply_zero A m
      map_add' := sectionBaseChangeInverseApply_add A m }

/-- The inverse ring map computes by the fiber inverse of the specified canonical map. -/
theorem sectionBaseChangeInverse_apply (A : X.QcAlgebraUnder) {U V : smallEtaleSite X}
    [IsAffine U.left.left] [IsAffine V.left.left] (m : U ⟶ V) (a : sectionRing A U) :
    (sectionBaseChangeInverse A m).hom a = sectionBaseChangeInverseApply A m a := rfl

end AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder
