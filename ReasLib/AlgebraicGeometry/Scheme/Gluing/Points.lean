module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Topology.Sheaves.Abelian
public import ReasLib.Algebra.Category.Ring.Sheaf.Additive
public import ReasLib.Algebra.Category.Ring.Sheaf.Units.Evaluation
public import ReasLib.AlgebraicGeometry.RingedSpace.Skyscraper
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Point

/-!
# Gluing points

Evaluation maps and exactness for identifying two rational points of an algebraic scheme.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace
open TopCat.Sheaf
open TopCat.Sheaf.Skyscraper
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The commutative-ring skyscraper sheaf at a point of a scheme. -/
noncomputable abbrev pointRingSheaf (X : Scheme.{u}) (x : X)
    (k : Type u) [CommRing k] : TopCat.Sheaf CommRingCat.{u} X.toTopCat :=
  atPoint x (CommRingCat.of k)

/-- The ordinary `Spec k`-valued point represented by a morphism from the chosen terminal scheme over `k`. -/
noncomputable abbrev SchemeOverField.rationalPoint {k : Type u} [Field k]
    {X : SchemeOverField k} (p : SchemeOverField.point k ⟶ X) :
    Spec (CommRingCat.of k) ⟶ X.left :=
  ((SchemeOverField.pointIsTerminal k).from
    (Over.mk (𝟙 (Spec (CommRingCat.of k))) : SchemeOverField k) ≫ p).left

/-- The structure-sheaf map `𝒰_X ⟶ f_*𝒰_Y`, viewed as a map of additive sheaves. -/
noncomputable abbrev additiveStructureMap {X Y : Scheme.{u}} (f : Y ⟶ X) :
    additiveSheaf X.sheaf ⟶
      additiveSheaf ((TopCat.Sheaf.pushforward CommRingCat f.base).obj Y.sheaf) :=
  additiveSheafMap (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom)

/-- The structure-sheaf map on units, represented in additive units sheaves. -/
noncomputable abbrev unitsStructureMap {X Y : Scheme.{u}} (f : Y ⟶ X) :
    CategoryTheory.Sheaf.unitsAddSheaf X.sheaf ⟶
      CategoryTheory.Sheaf.unitsAddSheaf
        ((TopCat.Sheaf.pushforward CommRingCat f.base).obj Y.sheaf) :=
  CategoryTheory.Sheaf.unitsAddMap
    (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom)

/-- A morphism from a pushforward structure sheaf is evaluation at a rational point above the support. -/
def IsEvaluationAt {k : Type u} [Field k]
    {X Y : Scheme.{u}} (f : Y ⟶ X) (p : Spec (CommRingCat.of k) ⟶ Y)
    (x : X)
    (eval : (TopCat.Sheaf.pushforward CommRingCat f.base).obj Y.sheaf ⟶
      TopCat.Sheaf.Skyscraper.atPoint x (CommRingCat.of k)) : Prop :=
  ∃ hpx : f (p (IsLocalRing.closedPoint k)) = x,
    (TopCat.Presheaf.stalkFunctor CommRingCat x).map eval.hom ≫
        (stalkIsoOfSpecializes x (CommRingCat.of k)
          (specializes_refl x)).hom =
      (((TopCat.Sheaf.pushforward CommRingCat f.base).obj Y.sheaf).presheaf.stalkCongr
        (Inseparable.of_eq hpx.symm)).hom ≫
          Y.presheaf.stalkPushforward CommRingCat f.base
            (p (IsLocalRing.closedPoint k)) ≫
          Scheme.stalkClosedPointTo p

/-- The defining stalk condition characterizes evaluation at a rational point. -/
theorem isEvaluationAt_iff {k : Type u} [Field k]
    {X Y : Scheme.{u}} (f : Y ⟶ X) (p : Spec (CommRingCat.of k) ⟶ Y)
    (x : X)
    (eval : (TopCat.Sheaf.pushforward CommRingCat f.base).obj Y.sheaf ⟶
      TopCat.Sheaf.Skyscraper.atPoint x (CommRingCat.of k)) :
    IsEvaluationAt f p x eval ↔
      ∃ hpx : f (p (IsLocalRing.closedPoint k)) = x,
        (TopCat.Presheaf.stalkFunctor CommRingCat x).map eval.hom ≫
            (stalkIsoOfSpecializes x (CommRingCat.of k)
              (specializes_refl x)).hom =
          (((TopCat.Sheaf.pushforward CommRingCat f.base).obj Y.sheaf).presheaf.stalkCongr
            (Inseparable.of_eq hpx.symm)).hom ≫
              Y.presheaf.stalkPushforward CommRingCat f.base
                (p (IsLocalRing.closedPoint k)) ≫
              Scheme.stalkClosedPointTo p := sorry

/-- Vanishing of the additive structure-map composite implies vanishing of the
    corresponding composite on units. -/
theorem unitsStructureMap_comp_evaluationDifference
    {k : Type u} [Field k] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (x : X)
    (evalA evalB : (TopCat.Sheaf.pushforward CommRingCat f.base).obj Y.sheaf ⟶
      TopCat.Sheaf.Skyscraper.atPoint x (CommRingCat.of k))
    (h_add_zero : additiveStructureMap f ≫
      additiveEvaluationDifference evalA evalB = 0) :
    unitsStructureMap f ≫ unitsEvaluationDifference evalA evalB = 0 := sorry

/-- A finite point-identifying morphism with an additive exactness sequence induces units exactness. -/
theorem unitsShortExact_of_glueingPoints
    {k : Type u} [Field k] [IsAlgClosed k]
    (X X' : SchemeOverField k) [Algebraic X] [Algebraic X']
    (f : X' ⟶ X) [IsFinite f.left]
    (a b : SchemeOverField.point k ⟶ X')
    (x : SchemeOverField.point k ⟶ X)
    (h_distinct : a ≠ b)
    (ha : a ≫ f = x) (hb : b ≫ f = x)
    (U : X.left.Opens)
    (hU : (U : Set X.left) =
      {SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)}ᶜ)
    [IsIso (f.left ∣_ U)]
    (evalA evalB :
      (TopCat.Sheaf.pushforward CommRingCat f.left.base).obj X'.left.sheaf ⟶
        TopCat.Sheaf.Skyscraper.atPoint
          (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k))
          (CommRingCat.of k))
    (h_evalA : IsEvaluationAt f.left (SchemeOverField.rationalPoint a)
      (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) evalA)
    (h_evalB : IsEvaluationAt f.left (SchemeOverField.rationalPoint b)
      (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) evalB)
    (h_add_zero : additiveStructureMap f.left ≫
      additiveEvaluationDifference evalA evalB = 0)
    (h_add_exact : (ShortComplex.mk (additiveStructureMap f.left)
      (additiveEvaluationDifference evalA evalB) h_add_zero).ShortExact) :
      (ShortComplex.mk (unitsStructureMap f.left)
      (unitsEvaluationDifference evalA evalB)
      (unitsStructureMap_comp_evaluationDifference f.left
        (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k))
        evalA evalB h_add_zero)).ShortExact := sorry

end AlgebraicGeometry
