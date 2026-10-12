/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DerivedTower
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction.Composition

@[expose] public section

/-!
# Restricting a derived module tower to a cone ring

A cone over the underlying inverse system of rings supplies a homomorphism from its vertex to
every stage.  Derived restriction of scalars therefore turns a varying-ring `DerivedTower` into
an ordinary sequential inverse system over the fixed vertex ring.
@stack 0CQF
-/

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.DerivedTower

variable {A : SequentialInverseSystem CommRingCat.{u}}

/-- Stage `n` of a derived module tower, restricted to the vertex ring of a cone. -/
noncomputable abbrev restrictObj (T : DerivedTower A) (s : Cone A) (n : ℕ) :
    DerivedCategory (ModuleCat.{u, u} (s.pt : Type u)) :=
  (derivedRestrictionOfScalars (s.stageMap n).hom).obj (T.obj n)

/-- The fixed-base transition obtained by restricting the tower transition and comparing direct
with iterated restriction of scalars. -/
@[stacks 0CQF "fixed-base transition of a derived module tower"]
noncomputable def restrictStep (T : DerivedTower A) (s : Cone A) (n : ℕ) :
    T.restrictObj s (n + 1) ⟶ T.restrictObj s n :=
  (derivedRestrictionOfScalars (s.stageMap (n + 1)).hom).map (T.step n) ≫
    (DerivedRestriction.compObjIsoOfEq
      (s.stageMap (n + 1)).hom (A.stepMap n).hom (s.stageMap n).hom
      (congrArg CommRingCat.Hom.hom
        (s.w ((homOfLE (Nat.le_add_right n 1)).op)).symm)
      (T.obj n)).inv

/-- The sequential inverse system over a cone vertex obtained from a varying-ring derived module
tower by restriction of scalars. -/
@[stacks 0CQF "derived module tower over its inverse-limit ring"]
noncomputable def restrict (T : DerivedTower A) (s : Cone A) :
    SequentialInverseSystem (DerivedCategory (ModuleCat.{u, u} (s.pt : Type u))) :=
  Functor.ofOpSequence (X := fun n ↦ T.restrictObj s n) (T.restrictStep s)

/-- Evaluation of the fixed-base restriction tower at stage `n`. -/
@[simp]
theorem restrict_obj (T : DerivedTower A) (s : Cone A) (n : ℕ) :
    (T.restrict s).obj (Opposite.op n) = T.restrictObj s n := sorry

/-- The successor map of the fixed-base restriction tower is the canonical restricted
transition. -/
@[simp]
theorem restrict_stepMap (T : DerivedTower A) (s : Cone A) (n : ℕ) :
    (T.restrict s).stepMap n = T.restrictStep s n := sorry

end CategoryTheory.ModuleCat.DerivedTower
