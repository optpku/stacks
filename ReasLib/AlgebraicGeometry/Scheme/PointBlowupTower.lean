/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.IdealStalk
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject

/-!
# Point blowup towers

This file records an infinite tower of blowups at compatible closed points,
without including any arc which realizes that tower.
-/

@[expose] public section

noncomputable section

open CategoryTheory Topology

universe u

namespace AlgebraicGeometry.Scheme

/-- An infinite tower of blowups at compatible closed points over `(X, p)`. -/
structure PointBlowupTower (X : Scheme.{u}) (p : closedPoints X) where
  /-- The scheme at each stage. -/
  stage : ℕ → Scheme.{u}
  /-- The transition morphism from stage `i + 1` to stage `i`. -/
  step : ∀ i, stage (i + 1) ⟶ stage i
  /-- The marked closed point at each stage. -/
  point : ∀ i, closedPoints (stage i)
  /-- The identification of the initial stage with the base scheme. -/
  baseIso : stage 0 ≅ X
  /-- The marked point at stage zero agrees with `p`. -/
  point_zero : baseIso.hom (point 0).1 = p.1
  /-- Every transition sends the next marked point to the preceding marked point. -/
  point_succ : ∀ i, step i (point (i + 1)).1 = (point i).1
  /-- Every transition is the blowup of the reduced preceding marked point. -/
  step_isBlowup : ∀ i, IsBlowup (step i)
    (IdealSheafData.vanishingIdeal (PointClosure.closedSubset (point i).1))

namespace PointBlowupTower

/-- Construct a point blowup tower from explicit compatible stages, points, and transitions. -/
def fromStages {X : Scheme.{u}} (p : closedPoints X)
    (stage : ℕ → Scheme.{u}) (step : ∀ i, stage (i + 1) ⟶ stage i)
    (point : ∀ i, closedPoints (stage i)) (baseIso : stage 0 ≅ X)
    (point_zero : baseIso.hom (point 0).1 = p.1)
    (point_succ : ∀ i, step i (point (i + 1)).1 = (point i).1)
    (step_isBlowup : ∀ i, IsBlowup (step i)
      (IdealSheafData.vanishingIdeal (PointClosure.closedSubset (point i).1))) :
    PointBlowupTower X p where
  stage := stage
  step := step
  point := point
  baseIso := baseIso
  point_zero := point_zero
  point_succ := point_succ
  step_isBlowup := step_isBlowup

/-- The stages of a tower constructed with `fromStages` are the supplied stages. -/
theorem fromStages_stage {X : Scheme.{u}} (p : closedPoints X)
    (stage : ℕ → Scheme.{u}) (step : ∀ i, stage (i + 1) ⟶ stage i)
    (point : ∀ i, closedPoints (stage i)) (baseIso : stage 0 ≅ X)
    (point_zero : baseIso.hom (point 0).1 = p.1)
    (point_succ : ∀ i, step i (point (i + 1)).1 = (point i).1)
    (step_isBlowup : ∀ i, IsBlowup (step i)
      (IdealSheafData.vanishingIdeal (PointClosure.closedSubset (point i).1))) (i : ℕ) :
    (fromStages p stage step point baseIso point_zero point_succ step_isBlowup).stage i =
      stage i := sorry

/-- The recursively determined composite from stage `i` to the base scheme. -/
def toBase {X : Scheme.{u}} {p : closedPoints X} (S : PointBlowupTower X p) :
    ∀ i, S.stage i ⟶ X
  | 0 => S.baseIso.hom
  | i + 1 => S.step i ≫ S.toBase i

/-- The stage-zero composite is the chosen initial isomorphism. -/
theorem toBase_zero {X : Scheme.{u}} {p : closedPoints X}
    (S : PointBlowupTower X p) : S.toBase 0 = S.baseIso.hom := sorry

/-- The composites to the base are compatible with the transition maps. -/
theorem toBase_succ {X : Scheme.{u}} {p : closedPoints X}
    (S : PointBlowupTower X p) (i : ℕ) :
    S.step i ≫ S.toBase i = S.toBase (i + 1) := sorry

/-- Every marked point maps to the original marked point. -/
theorem toBase_point {X : Scheme.{u}} {p : closedPoints X}
    (S : PointBlowupTower X p) (i : ℕ) : S.toBase i (S.point i).1 = p.1 := sorry

/-- The reduced closed point center at stage `i`. -/
noncomputable def center {X : Scheme.{u}} {p : closedPoints X}
    (S : PointBlowupTower X p) (i : ℕ) : (S.stage i).IdealSheafData :=
  IdealSheafData.vanishingIdeal (PointClosure.closedSubset (S.point i).1)

/-- The center of the `i`th transition is the reduced vanishing ideal of its marked point. -/
theorem center_def {X : Scheme.{u}} {p : closedPoints X}
    (S : PointBlowupTower X p) (i : ℕ) :
    S.center i = IdealSheafData.vanishingIdeal
      (PointClosure.closedSubset (S.point i).1) := sorry

/-- The local homomorphism from the initial marked stalk to the stalk at stage `i`. -/
noncomputable def stalkMap {X : Scheme.{u}} {p : closedPoints X}
    (S : PointBlowupTower X p) (i : ℕ) :
    X.presheaf.stalk p.1 →+* (S.stage i).presheaf.stalk (S.point i).1 :=
  ((X.presheaf.stalkCongr (.of_eq (S.toBase_point i).symm)).hom ≫
    (S.toBase i).stalkMap (S.point i).1).hom

/-- The local homomorphism on stalks associated to a stage of a point blowup tower is local. -/
theorem stalkMap_isLocal {X : Scheme.{u}} {p : closedPoints X}
    (S : PointBlowupTower X p) (i : ℕ) : IsLocalHom (S.stalkMap i) := sorry

/-- The exceptional divisor on stage `i + 1` is the pullback of the preceding point center. -/
noncomputable def exceptionalDivisor {X : Scheme.{u}} {p : closedPoints X}
    (S : PointBlowupTower X p) (i : ℕ) : (S.stage (i + 1)).IdealSheafData :=
  (S.center i).comap (S.step i)

/-- The exceptional divisor is the pullback of the reduced marked-point center. -/
theorem exceptionalDivisor_def {X : Scheme.{u}} {p : closedPoints X}
    (S : PointBlowupTower X p) (i : ℕ) :
    S.exceptionalDivisor i = (S.center i).comap (S.step i) := sorry

/-- The stalk ideal of the `i`th exceptional divisor at the next marked point. -/
noncomputable def exceptionalStalkIdeal {X : Scheme.{u}} {p : closedPoints X}
    (S : PointBlowupTower X p) (i : ℕ) :
    Ideal ((S.stage (i + 1)).presheaf.stalk (S.point (i + 1)).1) :=
  RingedSpace.idealSheafStalkIdeal (S.exceptionalDivisor i).toSubobject
    (S.point (i + 1)).1

/-- The exceptional stalk ideal is the image ideal of the pulled-back point center. -/
theorem exceptionalStalkIdeal_def {X : Scheme.{u}} {p : closedPoints X}
    (S : PointBlowupTower X p) (i : ℕ) :
    S.exceptionalStalkIdeal i =
      RingedSpace.idealSheafStalkIdeal (S.exceptionalDivisor i).toSubobject
        (S.point (i + 1)).1 := sorry

/-- Every transition of the tower induces a bijection on residue fields at the marked points. -/
def PreservesResidueFields {X : Scheme.{u}} {p : closedPoints X}
    (S : PointBlowupTower X p) : Prop :=
  ∀ i, Function.Bijective ((S.step i).residueFieldMap (S.point (i + 1)).1)

/-- Residue-field preservation is the stagewise bijectivity of the canonical residue maps. -/
theorem preservesResidueFields_iff {X : Scheme.{u}} {p : closedPoints X}
    (S : PointBlowupTower X p) :
    S.PreservesResidueFields ↔
      ∀ i, Function.Bijective ((S.step i).residueFieldMap (S.point (i + 1)).1) := sorry

/-- One element of the initial maximal ideal generates every exceptional-divisor stalk ideal. -/
def HasCommonExceptionalGenerator {X : Scheme.{u}} {p : closedPoints X}
    (S : PointBlowupTower X p) : Prop :=
  ∃ x₁ : IsLocalRing.maximalIdeal (X.presheaf.stalk p.1), ∀ i,
    S.exceptionalStalkIdeal i =
      Ideal.span ({S.stalkMap (i + 1) x₁.1} : Set
        ((S.stage (i + 1)).presheaf.stalk (S.point (i + 1)).1))

/-- The common-generator condition exposes one initial element and its condition at every
positive stage. -/
theorem hasCommonExceptionalGenerator_iff {X : Scheme.{u}} {p : closedPoints X}
    (S : PointBlowupTower X p) :
    S.HasCommonExceptionalGenerator ↔
      ∃ x₁ : IsLocalRing.maximalIdeal (X.presheaf.stalk p.1), ∀ i,
        S.exceptionalStalkIdeal i =
          Ideal.span ({S.stalkMap (i + 1) x₁.1} : Set
            ((S.stage (i + 1)).presheaf.stalk (S.point (i + 1)).1)) := sorry

/-- The marked-point and blowup conditions defining a point blowup tower. -/
theorem spec {X : Scheme.{u}} {p : closedPoints X} (S : PointBlowupTower X p) :
    (S.baseIso.hom (S.point 0).1 = p.1) ∧
      (∀ i, S.step i (S.point (i + 1)).1 = (S.point i).1) ∧
      (∀ i, IsBlowup (S.step i)
        (IdealSheafData.vanishingIdeal (PointClosure.closedSubset (S.point i).1))) := sorry

/-- Compatible lifts of a pointed morphism through every stage of a point blowup tower. -/
structure Lift {X : Scheme.{u}} {p : closedPoints X} (S : PointBlowupTower X p)
    {T : Scheme.{u}} (a : T ⟶ X) (t : T) where
  /-- The lifted morphism at each stage. -/
  arc : ∀ i, T ⟶ S.stage i
  /-- The stage-zero lift agrees with the original morphism. -/
  arc_zero : arc 0 ≫ S.baseIso.hom = a
  /-- Successive lifts commute with the transition morphisms. -/
  arc_succ : ∀ i, arc (i + 1) ≫ S.step i = arc i
  /-- The marked source point maps to the marked point at every stage. -/
  point_eq : ∀ i, arc i t = (S.point i).1

namespace Lift

/-- Construct compatible lifts from an explicit family of stage morphisms and its compatibility
laws. -/
def ofArcs {X : Scheme.{u}} {p : closedPoints X} (S : PointBlowupTower X p)
    {T : Scheme.{u}} (a : T ⟶ X) (t : T) (arc : ∀ i, T ⟶ S.stage i)
    (arc_zero : arc 0 ≫ S.baseIso.hom = a)
    (arc_succ : ∀ i, arc (i + 1) ≫ S.step i = arc i)
    (point_eq : ∀ i, arc i t = (S.point i).1) : S.Lift a t where
  arc := arc
  arc_zero := arc_zero
  arc_succ := arc_succ
  point_eq := point_eq

/-- The stage morphisms of a lift constructed by `ofArcs` are the supplied morphisms. -/
theorem ofArcs_arc {X : Scheme.{u}} {p : closedPoints X} (S : PointBlowupTower X p)
    {T : Scheme.{u}} (a : T ⟶ X) (t : T) (arc : ∀ i, T ⟶ S.stage i)
    (arc_zero : arc 0 ≫ S.baseIso.hom = a)
    (arc_succ : ∀ i, arc (i + 1) ≫ S.step i = arc i)
    (point_eq : ∀ i, arc i t = (S.point i).1) (i : ℕ) :
    (ofArcs S a t arc arc_zero arc_succ point_eq).arc i = arc i := sorry

/-- The base, successor, and marked-point conditions defining a compatible lift. -/
theorem spec {X : Scheme.{u}} {p : closedPoints X} (S : PointBlowupTower X p)
    {T : Scheme.{u}} {a : T ⟶ X} {t : T} (L : S.Lift a t) :
    (L.arc 0 ≫ S.baseIso.hom = a) ∧
      (∀ i, L.arc (i + 1) ≫ S.step i = L.arc i) ∧
      (∀ i, L.arc i t = (S.point i).1) := sorry

end Lift

end PointBlowupTower

end AlgebraicGeometry.Scheme
