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
      (t.truncGE (index (1 + n))).obj (DerivedCategory.Q.obj K) := rfl

/-- The target object at stage `n` is the derived image of the concrete lower
truncation at cutoff `-(n + 1)`. -/
@[simp, stacks 070F, stacks 0H72]
theorem derivedTower_obj (K : CochainComplex A ℤ) (n : ℕ) :
    (CochainComplex.LowerTruncation.derivedTower K).obj (op n) =
      DerivedCategory.Q.obj (CochainComplex.LowerTruncation.stage K n) := rfl

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
    IsIso (stageHom K n) := by
  have hq (a : ℤ) : IsIso (TruncGE.qHom K a) := by
    have hg : IsIso ((t.truncGE a).map
        (DerivedCategory.Q.map (K.shortComplexTruncLE (a - 1)).g)) := by
      apply t.isIso₂_truncGE_map_of_isLE
        (DerivedCategory.triangleOfSES (K.shortComplexTruncLE_shortExact (a - 1)))
        (DerivedCategory.triangleOfSES_distinguished (K.shortComplexTruncLE_shortExact (a - 1)))
        (a - 1) a (by omega)
      change (DerivedCategory.Q.obj (K.truncLE (a - 1))).IsLE (a - 1)
      infer_instance
    letI := hg
    haveI : IsIso ((t.truncGE a).map (DerivedCategory.Q.map (K.πTruncGE a))) := by
      rw [← K.g_shortComplexTruncLEX₃ToTruncGE (a - 1) a (by omega)]
      change IsIso ((t.truncGE a).map (DerivedCategory.Q.map
        ((K.shortComplexTruncLE (a - 1)).g ≫
          K.shortComplexTruncLEX₃ToTruncGE (a - 1) a (by omega))))
      rw [DerivedCategory.Q.map_comp, (t.truncGE a).map_comp]
      infer_instance
    have hfac :
        (t.truncGEπ a).app (DerivedCategory.Q.obj K) ≫
          ((t.truncGE a).map (DerivedCategory.Q.map (K.πTruncGE a)) ≫
            inv ((t.truncGEπ a).app (DerivedCategory.Q.obj (K.truncGE a)))) =
          DerivedCategory.Q.map (K.πTruncGE a) := by
      rw [← Category.assoc, ← (t.truncGEπ a).naturality]
      simp only [Functor.id_map, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    have heq : TruncGE.qHom K a =
        (t.truncGE a).map (DerivedCategory.Q.map (K.πTruncGE a)) ≫
          inv ((t.truncGEπ a).app (DerivedCategory.Q.obj (K.truncGE a))) := by
      apply t.from_truncGE_obj_ext
      rw [TruncGE.qHom, t.π_descTruncGE]
      exact hfac.symm
    rw [heq]
    exact inferInstanceAs (IsIso ((t.truncGE a).map (DerivedCategory.Q.map (K.πTruncGE a)) ≫
      inv ((t.truncGEπ a).app (DerivedCategory.Q.obj (K.truncGE a)))))
  letI := hq (index (1 + n))
  exact inferInstanceAs (IsIso (TruncGE.qHom K (index (1 + n)) ≫
    DerivedCategory.Q.map (indexIso K n).hom))

/-- The stage comparison identifies the canonical maps from `Q.obj K` to the
two lower-truncation models. -/
@[reassoc (attr := simp), stacks 070F, stacks 0H72]
theorem toStage_comp_stageHom (K : CochainComplex A ℤ) (n : ℕ) :
    toStage (DerivedCategory.Q.obj K) (1 + n) ≫ stageHom K n =
      CochainComplex.LowerTruncation.derivedToStage K n := by
  change (t.truncGEπ (index (1 + n))).app (DerivedCategory.Q.obj K) ≫
      (TruncGE.qHom K (index (1 + n)) ≫ DerivedCategory.Q.map (indexIso K n).hom) =
    DerivedCategory.Q.map (K.πTruncGE (CochainComplex.LowerTruncation.index n))
  rw [← Category.assoc, TruncGE.qHom, t.π_descTruncGE]
  exact (DerivedCategory.Q.map_comp _ _).symm.trans
    (congrArg DerivedCategory.Q.map
      (by simpa only [indexIso, index, CochainComplex.LowerTruncation.stage,
          CochainComplex.LowerTruncation.index, eqToIso.hom, eqToHom_refl,
          Category.id_comp] using
        eqToHom_naturality (fun m : ℕ ↦ K.πTruncGE (-(m : ℤ))) (Nat.one_add n)))

/-- The derived concrete tower's successor map is the derived image of its
declared concrete lower-truncation transition. -/
@[simp, stacks 070F, stacks 0H72]
theorem derivedTower_stepMap (K : CochainComplex A ℤ) (n : ℕ) :
    (CochainComplex.LowerTruncation.derivedTower K).stepMap n =
      DerivedCategory.Q.map (CochainComplex.LowerTruncation.step K n) := by
  exact congrArg DerivedCategory.Q.map
    (Functor.ofOpSequence_map_homOfLE_succ
      (CochainComplex.LowerTruncation.step K) n)

/-- Successive stage comparisons commute with the transition maps of the two
lower-truncation towers. -/
@[stacks 070F, stacks 0H72]
theorem stageHom_naturality (K : CochainComplex A ℤ) (n : ℕ) :
    ((tower (DerivedCategory.Q.obj K)).shift 1).stepMap n ≫ stageHom K n =
      stageHom K (n + 1) ≫
        (CochainComplex.LowerTruncation.derivedTower K).stepMap n := by
  have hq {a b : ℤ} (hab : a ≤ b) :
      (t.natTransTruncGEOfLE a b hab).app (DerivedCategory.Q.obj K) ≫ TruncGE.qHom K b =
        TruncGE.qHom K a ≫ DerivedCategory.Q.map (CochainComplex.truncGEMapOfLE K hab) := by
    letI : (K.truncGE b).IsStrictlyGE a := (K.truncGE b).isStrictlyGE_of_ge a b hab
    apply t.from_truncGE_obj_ext
    have hπ : K.πTruncGE a ≫ CochainComplex.truncGEMapOfLE K hab = K.πTruncGE b := by
      dsimp only [CochainComplex.truncGEMapOfLE]
      rw [← Category.assoc, CochainComplex.πTruncGE_naturality, Category.assoc,
        IsIso.hom_inv_id, Category.comp_id]
    calc
      _ = DerivedCategory.Q.map (K.πTruncGE b) := by
        rw [← Category.assoc, t.π_natTransTruncGEOfLE_app, TruncGE.qHom, t.π_descTruncGE]
      _ = _ := by
        rw [← Category.assoc, TruncGE.qHom, t.π_descTruncGE]
        exact (congrArg DerivedCategory.Q.map hπ).symm.trans (DerivedCategory.Q.map_comp _ _)
  have hstep : (tower (DerivedCategory.Q.obj K)).stepMap (1 + n) =
      (t.natTransTruncGEOfLE (index (1 + (n + 1))) (index (1 + n))
        (neg_le_neg (Int.ofNat_le_ofNat_of_le (Nat.le_succ (1 + n))))).app
          (DerivedCategory.Q.obj K) :=
    Functor.ofOpSequence_map_homOfLE_succ _ (1 + n)
  change (tower (DerivedCategory.Q.obj K)).stepMap (1 + n) ≫ _ = _
  rw [hstep, derivedTower_stepMap]
  change (t.natTransTruncGEOfLE _ _ _).app (DerivedCategory.Q.obj K) ≫
      (TruncGE.qHom K (index (1 + n)) ≫ DerivedCategory.Q.map (indexIso K n).hom) =
    (TruncGE.qHom K (index (1 + (n + 1))) ≫
      DerivedCategory.Q.map (indexIso K (n + 1)).hom) ≫
        DerivedCategory.Q.map (CochainComplex.LowerTruncation.step K n)
  rw [← Category.assoc, hq]
  simp only [Category.assoc, ← DerivedCategory.Q.map_comp]
  apply congrArg (fun f ↦ TruncGE.qHom K (index (1 + (n + 1))) ≫ DerivedCategory.Q.map f)
  exact eqToHom_naturality
    (fun m : ℕ ↦ CochainComplex.truncGEMapOfLE K
      (neg_le_neg (Int.ofNat_le_ofNat_of_le (Nat.le_succ m)))) (Nat.one_add n)

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
    (towerHom K).app (op n) = stageHom K n := rfl

/-- The tower comparison commutes with every transition map, not only the
successor transitions used in its construction. -/
@[reassoc, stacks 070F, stacks 0H72]
theorem transitionMap_comp_towerHom_app (K : CochainComplex A ℤ)
    {m n : ℕ} (h : m ≤ n) :
    ((tower (DerivedCategory.Q.obj K)).shift 1).transitionMap h ≫
        (towerHom K).app (op m) =
      (towerHom K).app (op n) ≫
        (CochainComplex.LowerTruncation.derivedTower K).transitionMap h := by
  exact (towerHom K).naturality (homOfLE h).op

/-- The canonical comparison of lower-truncation towers is an isomorphism. -/
@[stacks 070F, stacks 0H72]
instance towerHom_isIso (K : CochainComplex A ℤ) :
    IsIso (towerHom K) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  change IsIso (stageHom K n.unop)
  exact stageHom_isIso K n.unop

end CategoryTheory.DerivedCategory.Truncation.Lower.Cochain
