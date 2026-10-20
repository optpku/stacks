/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DerivedExtension.Composition
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DerivedTower.Restriction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Explicit Derived Extension Models Along a Cone

A cone over a sequential inverse system of commutative rings supplies maps from its vertex ring
to every stage.  A `DerivedExtension.ConeModel` records explicit derived extension models along
those stage maps and along the successor maps of the system.  Canonical comparison isomorphisms
for composite extension then assemble the base changes of one derived module into a varying-ring
derived tower and, after restriction, a fixed-base inverse system under the original module.
@stack 064M
@stack 0CQF
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.DerivedExtension

variable {A : SequentialInverseSystem CommRingCat.{u}}

/-- Explicit derived extension models along every leg and every successor map of a cone over a
sequential inverse system of commutative rings. -/
@[stacks 0CQF "explicit derived extension models along a ring inverse-system cone"]
structure ConeModel (s : Cone A) where
  /-- The explicit extension model from the cone vertex to stage `n`. -/
  stage (n : ℕ) : DerivedExtension (s.stageMap n).hom
  /-- The explicit extension model along the successor map from stage `n + 1` to stage `n`. -/
  step (n : ℕ) : DerivedExtension (A.stepMap n).hom

namespace ConeModel

variable {s : Cone A}

/-- The canonical comparison from iterated extension through stage `n + 1` to direct extension
from the cone vertex to stage `n`. -/
@[stacks 064M "iterated-to-direct extension comparison along a cone"]
noncomputable abbrev stepComparison (E : ConeModel s)
    (K : DerivedCategory (ModuleCat.{u, u} (s.pt : Type u))) (n : ℕ) :
    (E.step n).obj ((E.stage (n + 1)).obj K) ⟶ (E.stage n).obj K :=
  (compObjIsoOfEq (s.stageMap n).hom
    (E.stage (n + 1)) (E.step n) (E.stage n)
    (congrArg CommRingCat.Hom.hom
      (s.w ((homOfLE (Nat.le_add_right n 1)).op)).symm) K).hom

/-- The varying-ring derived tower obtained by explicitly extending `K` to every stage of the
cone and using the canonical composition comparisons as base-change maps. -/
@[stacks 0CQF "derived base-change tower along a ring inverse-system cone"]
noncomputable def tower (E : ConeModel s)
    (K : DerivedCategory (ModuleCat.{u, u} (s.pt : Type u))) : DerivedTower A :=
  DerivedTower.ofBaseChange E.step
    (fun n ↦ (E.stage n).obj K)
    (fun n ↦ E.stepComparison K n)

/-- The stage objects of the tower associated to a cone model are the supplied explicit stage
extensions. -/
@[simp]
theorem tower_obj (E : ConeModel s)
    (K : DerivedCategory (ModuleCat.{u, u} (s.pt : Type u))) (n : ℕ) :
    (E.tower K).obj n = (E.stage n).obj K := sorry

/-- The successor morphism of the tower associated to a cone model is adjoint to its canonical
iterated-to-direct extension comparison. -/
theorem tower_step (E : ConeModel s)
    (K : DerivedCategory (ModuleCat.{u, u} (s.pt : Type u))) (n : ℕ) :
    (E.tower K).step n = (E.step n).untranspose (E.stepComparison K n) := sorry

/-- Base change of the tower associated to a cone model recovers the canonical composition
comparison used to construct it. -/
@[simp]
theorem tower_baseChangeMap (E : ConeModel s)
    (K : DerivedCategory (ModuleCat.{u, u} (s.pt : Type u))) (n : ℕ) :
    (E.tower K).baseChangeMap n (E.step n) = E.stepComparison K n := sorry

/-- The tower associated to an explicit cone model is Cartesian. -/
@[stacks 0CQF "explicit derived base-change towers are Cartesian"]
theorem tower_isCartesian (E : ConeModel s)
    (K : DerivedCategory (ModuleCat.{u, u} (s.pt : Type u))) :
    (E.tower K).IsCartesian := sorry

/-- The fixed-base inverse system obtained by restricting the explicit derived extension tower
back to the vertex ring of the cone. -/
@[stacks 0CQF "fixed-base derived extension system along a cone"]
noncomputable abbrev system (E : ConeModel s)
    (K : DerivedCategory (ModuleCat.{u, u} (s.pt : Type u))) :
    SequentialInverseSystem (DerivedCategory (ModuleCat.{u, u} (s.pt : Type u))) :=
  (E.tower K).restrict s

/-- Stage `n` of the fixed-base system is the explicit stage extension restricted back to the
cone vertex ring. -/
@[simp]
theorem system_obj (E : ConeModel s)
    (K : DerivedCategory (ModuleCat.{u, u} (s.pt : Type u))) (n : ℕ) :
    (E.system K).obj (op n) =
      (derivedRestrictionOfScalars (s.stageMap n).hom).obj ((E.stage n).obj K) := sorry

/-- The successor map of the fixed-base system is the canonical restriction of the varying-ring
tower transition. -/
@[simp]
theorem system_stepMap (E : ConeModel s)
    (K : DerivedCategory (ModuleCat.{u, u} (s.pt : Type u))) (n : ℕ) :
    (E.system K).stepMap n = (E.tower K).restrictStep s n := sorry

/-- The stagewise comparison between the fixed-base systems produced by two explicit cone
models. -/
noncomputable def systemIsoApp (E F : ConeModel s)
    (K : DerivedCategory (ModuleCat.{u, u} (s.pt : Type u))) (n : ℕ) :
    (E.system K).obj (op n) ≅ (F.system K).obj (op n) :=
  (derivedRestrictionOfScalars (s.stageMap n).hom).mapIso
    (((E.stage n).iso (F.stage n)).app K)

/-- The stagewise model comparisons commute with every map of the fixed-base inverse systems. -/
theorem systemIsoApp_hom_naturality (E F : ConeModel s)
    (K : DerivedCategory (ModuleCat.{u, u} (s.pt : Type u)))
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (E.system K).map f ≫ (E.systemIsoApp F K j.unop).hom =
      (E.systemIsoApp F K i.unop).hom ≫ (F.system K).map f := sorry

/-- The fixed-base inverse system obtained from a cone model is independent, up to canonical
natural isomorphism, of every explicit derived extension model used in its construction. -/
@[stacks 064M "model independence of a derived extension system"]
noncomputable def systemIso (E F : ConeModel s)
    (K : DerivedCategory (ModuleCat.{u, u} (s.pt : Type u))) :
    E.system K ≅ F.system K :=
  NatIso.ofComponents (fun n ↦ E.systemIsoApp F K n.unop)
    (fun f ↦ E.systemIsoApp_hom_naturality F K f)

/-- Components of the system comparison are the restricted uniqueness isomorphisms between the
corresponding stage extension models. -/
@[simp]
theorem systemIso_hom_app (E F : ConeModel s)
    (K : DerivedCategory (ModuleCat.{u, u} (s.pt : Type u))) (n : ℕ) :
    (E.systemIso F K).hom.app (op n) = (E.systemIsoApp F K n).hom := sorry

/-- The adjunction unit from `K` to stage `n` of the fixed-base derived extension system. -/
@[stacks 0CQF "unit map to a stage of a derived extension system"]
noncomputable def unitAt (E : ConeModel s)
    (K : DerivedCategory (ModuleCat.{u, u} (s.pt : Type u))) (n : ℕ) :
    K ⟶ (E.system K).obj (op n) :=
  (E.stage n).adjunction.unit.app K

/-- The stagewise adjunction units commute with the successor maps of the fixed-base system. -/
theorem unitAt_step (E : ConeModel s)
    (K : DerivedCategory (ModuleCat.{u, u} (s.pt : Type u))) (n : ℕ) :
    E.unitAt K (n + 1) ≫ (E.system K).stepMap n = E.unitAt K n := sorry

/-- Naturality of the stagewise adjunction units in the form required by
`NatTrans.ofOpSequence`. -/
theorem unitAt_naturality (E : ConeModel s)
    (K : DerivedCategory (ModuleCat.{u, u} (s.pt : Type u))) (n : ℕ) :
    ((Functor.const ℕᵒᵖ).obj K).map (homOfLE (Nat.le_add_right n 1)).op ≫
        E.unitAt K n =
      E.unitAt K (n + 1) ≫
        (E.system K).map (homOfLE (Nat.le_add_right n 1)).op := sorry

/-- The canonical comparison between two explicit cone models carries the adjunction unit of the
first model to the adjunction unit of the second. -/
@[reassoc]
theorem unitAt_systemIso_hom (E F : ConeModel s)
    (K : DerivedCategory (ModuleCat.{u, u} (s.pt : Type u))) (n : ℕ) :
    E.unitAt K n ≫ (E.systemIso F K).hom.app (op n) = F.unitAt K n := sorry

/-- The canonical cone from `K` to its fixed-base derived extension system. -/
@[stacks 0CQF "unit cone to a derived extension system"]
noncomputable def unitCone (E : ConeModel s)
    (K : DerivedCategory (ModuleCat.{u, u} (s.pt : Type u))) : Cone (E.system K) where
  pt := K
  π := NatTrans.ofOpSequence
    (F := (Functor.const ℕᵒᵖ).obj K) (G := E.system K)
    (fun n ↦ E.unitAt K n) (E.unitAt_naturality K)

/-- The vertex of the unit cone is the original derived module. -/
@[simp]
theorem unitCone_pt (E : ConeModel s)
    (K : DerivedCategory (ModuleCat.{u, u} (s.pt : Type u))) :
    (E.unitCone K).pt = K := sorry

/-- The `n`th leg of the unit cone is the stagewise adjunction unit. -/
@[simp]
theorem unitCone_stageMap (E : ConeModel s)
    (K : DerivedCategory (ModuleCat.{u, u} (s.pt : Type u))) (n : ℕ) :
    (E.unitCone K).stageMap n = E.unitAt K n := sorry

end ConeModel

end CategoryTheory.ModuleCat.DerivedExtension
