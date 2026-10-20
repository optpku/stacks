/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Truncation.LowerResolution.Derived
public import ReasLib.CategoryTheory.DerivedCategory.Truncation.Cochain
public import ReasLib.CategoryTheory.DerivedCategory.Truncation.Lower.Tower

@[expose] public section

/-!
# Cochain Model of the Lower Derived-Truncation Tower

The lower derived-truncation tower of `Q.obj K`, after deleting its degree-zero
stage, agrees with the derived image of the concrete lower-truncation tower of
`K`.  This file exposes the canonical comparison natural transformation and
its stage and transition formulas.
-/

open CategoryTheory Opposite
open DerivedCategory.TStructure

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory.Truncation.Lower.Cochain

variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A]

/-- The explicit reindexing isomorphism identifying cutoff `-(1 + n)` with
the concrete tower cutoff `-(n + 1)`. -/
@[stacks 070F, stacks 0H72]
noncomputable def indexIso (K : CochainComplex A ℤ) (n : ℕ) :
    K.truncGE (index (1 + n)) ≅
      CochainComplex.LowerTruncation.stage K n :=
  eqToIso
    (congrArg (fun m : ℕ ↦ K.truncGE (-(m : ℤ))) (Nat.one_add n))

/-- The source object at stage `n` of the shifted abstract tower is the
abstract lower truncation at cutoff `-(1 + n)`. -/
@[simp, stacks 070F, stacks 0H72]
theorem shift_obj (K : CochainComplex A ℤ) (n : ℕ) :
    ((tower (DerivedCategory.Q.obj K)).shift 1).obj (op n) =
      (t.truncGE (index (1 + n))).obj (DerivedCategory.Q.obj K) := sorry

/-- The target object at stage `n` is the derived image of the concrete lower
truncation at cutoff `-(n + 1)`. -/
@[simp, stacks 070F, stacks 0H72]
theorem derivedTower_obj (K : CochainComplex A ℤ) (n : ℕ) :
    (CochainComplex.LowerTruncation.derivedTower K).obj (op n) =
      DerivedCategory.Q.obj (CochainComplex.LowerTruncation.stage K n) := sorry

/-- The canonical stage comparison from the shifted abstract truncation tower
to the derived concrete truncation tower. -/
@[stacks 070F, stacks 0H72]
noncomputable def stageHom (K : CochainComplex A ℤ) (n : ℕ) :
    ((tower (DerivedCategory.Q.obj K)).shift 1).obj (op n) ⟶
      (CochainComplex.LowerTruncation.derivedTower K).obj (op n) :=
  TruncGE.qHom K (index (1 + n)) ≫
    DerivedCategory.Q.map (indexIso K n).hom

/-- Every canonical stage comparison is an isomorphism. -/
@[stacks 070F, stacks 0H72]
instance stageHom_isIso (K : CochainComplex A ℤ) (n : ℕ) :
    IsIso (stageHom K n) := sorry

/-- The stage comparison identifies the canonical maps from `Q.obj K` to the
two lower-truncation models. -/
@[reassoc (attr := simp), stacks 070F, stacks 0H72]
theorem toStage_comp_stageHom (K : CochainComplex A ℤ) (n : ℕ) :
    toStage (DerivedCategory.Q.obj K) (1 + n) ≫ stageHom K n =
      CochainComplex.LowerTruncation.derivedToStage K n := sorry

/-- The derived concrete tower's successor map is the derived image of its
declared concrete lower-truncation transition. -/
@[simp, stacks 070F, stacks 0H72]
theorem derivedTower_stepMap (K : CochainComplex A ℤ) (n : ℕ) :
    (CochainComplex.LowerTruncation.derivedTower K).stepMap n =
      DerivedCategory.Q.map (CochainComplex.LowerTruncation.step K n) := sorry

/-- Successive stage comparisons commute with the transition maps of the two
lower-truncation towers. -/
@[stacks 070F, stacks 0H72]
theorem stageHom_naturality (K : CochainComplex A ℤ) (n : ℕ) :
    ((tower (DerivedCategory.Q.obj K)).shift 1).stepMap n ≫ stageHom K n =
      stageHom K (n + 1) ≫
        (CochainComplex.LowerTruncation.derivedTower K).stepMap n := sorry

/-- The canonical comparison from the shifted abstract lower-truncation tower
to the derived concrete lower-truncation tower. -/
@[stacks 070F, stacks 0H72]
noncomputable def towerHom (K : CochainComplex A ℤ) :
    (tower (DerivedCategory.Q.obj K)).shift 1 ⟶
      CochainComplex.LowerTruncation.derivedTower K :=
  NatTrans.ofOpSequence (stageHom K) (stageHom_naturality K)

/-- The component of the tower comparison is the canonical stage
comparison. -/
@[simp, stacks 070F, stacks 0H72]
theorem towerHom_app (K : CochainComplex A ℤ) (n : ℕ) :
    (towerHom K).app (op n) = stageHom K n := sorry

/-- The tower comparison commutes with every transition map, not only the
successor transitions used in its construction. -/
@[reassoc, stacks 070F, stacks 0H72]
theorem transitionMap_comp_towerHom_app (K : CochainComplex A ℤ)
    {m n : ℕ} (h : m ≤ n) :
    ((tower (DerivedCategory.Q.obj K)).shift 1).transitionMap h ≫
        (towerHom K).app (op m) =
      (towerHom K).app (op n) ≫
        (CochainComplex.LowerTruncation.derivedTower K).transitionMap h := sorry

/-- The canonical comparison of lower-truncation towers is an isomorphism. -/
@[stacks 070F, stacks 0H72]
instance towerHom_isIso (K : CochainComplex A ℤ) :
    IsIso (towerHom K) := sorry

end CategoryTheory.DerivedCategory.Truncation.Lower.Cochain
