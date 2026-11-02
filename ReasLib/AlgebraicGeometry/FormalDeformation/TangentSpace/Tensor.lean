/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.SquareZeroFunctor
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Functor
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger.Types
public import ReasLib.CategoryTheory.Cofibered.FiberIsoClass

/-!
# Tangent-space module structure and tensor comparison

If `F-bar` satisfies Schlessinger's (H2), the fibrewise isomorphism-class value
`F-bar(k[ε])` carries a natural `k`-vector space structure, and the values
`F-bar(k[V])` compare with `F-bar(k[ε]) ⊗[k] V`.
-/

@[expose] public section

open scoped Module.CommOpposite

noncomputable section

open CategoryTheory hiding Linear
open CategoryTheory.Limits
open ArtinianLocalAlgCat
open FGModuleCat
open scoped TensorProduct

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

/-- Evaluation of a functor on finitely generated square-zero extensions `k[V]`. -/
def squareZeroEval (F : ArtinianLocalAlgCat Λ k ⥤ Type v) : FGModuleCat.{u} k ⥤ Type v :=
  squareZeroFunctor Λ k ⋙ F

/-- Evaluation of `squareZeroEval` at `V` is `F.obj (squareZero Λ k V)`. -/
theorem squareZeroEval_obj (F : ArtinianLocalAlgCat Λ k ⥤ Type v) (V : FGModuleCat.{u} k) :
    (squareZeroEval F).obj V = F.obj (squareZero Λ k V) :=
  rfl

/-- `squareZeroEval` acts on morphisms by the underlying action of `F`. -/
theorem squareZeroEval_map (F : ArtinianLocalAlgCat Λ k ⥤ Type v) {V W : FGModuleCat.{u} k}
    (f : V ⟶ W) :
    (squareZeroEval F).map f = F.map ((squareZeroFunctor Λ k).map f) :=
  rfl

variable {F : Type v} [Category.{w} F]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k)

/-- The unique isomorphism class in the residue fibre of a predeformation category. -/
def fiberResidueClass [IsPredeformationCategory p] :
    (fiberIsoClassFunctor p).obj (residue Λ k) := by
  have existence : ∃! point : (fiberIsoClassFunctor p).obj (residue Λ k),
      ∀ value, value = point := by
    obtain ⟨representative⟩ := IsPredeformationCategory.nonempty_residueFiber (p := p)
    have uniqueness : ∀ value : (fiberIsoClassFunctor p).obj (residue Λ k),
        value = Quotient.mk'' representative := by
      intro value
      induction value using Quotient.inductionOn with
      | h object =>
        obtain ⟨forward⟩ := (IsPredeformationCategory.unique_residueHom object representative).1
        obtain ⟨backward⟩ := (IsPredeformationCategory.unique_residueHom representative object).1
        apply Quotient.sound
        exact ⟨{ hom := forward, inv := backward
                 hom_inv_id := (IsPredeformationCategory.unique_residueHom object object).2.elim _ _
                 inv_hom_id := (IsPredeformationCategory.unique_residueHom representative representative).2.elim _ _ }⟩
    exact ⟨Quotient.mk'' representative, uniqueness, fun point property ↦
      (property (Quotient.mk'' representative)).symm⟩
  exact existence.choose

/-- Every residue-fibre isomorphism class equals the distinguished residue class. -/
theorem fiberResidueClass_spec [IsPredeformationCategory p]
    (value : (fiberIsoClassFunctor p).obj (residue Λ k)) :
    value = fiberResidueClass p := by
  induction value using Quotient.inductionOn with
  | h object =>
    induction fiberResidueClass p using Quotient.inductionOn with
    | h representative =>
      obtain ⟨forward⟩ := (IsPredeformationCategory.unique_residueHom object representative).1
      obtain ⟨backward⟩ := (IsPredeformationCategory.unique_residueHom representative object).1
      apply Quotient.sound
      exact ⟨{ hom := forward, inv := backward
               hom_inv_id := (IsPredeformationCategory.unique_residueHom object object).2.elim _ _
               inv_hom_id := (IsPredeformationCategory.unique_residueHom representative representative).2.elim _ _ }⟩

/-- The residue-fibre isomorphism classes form the singleton with its specified residue class. -/
instance instUnique_fiberIsoClass_residue [IsPredeformationCategory p] :
    Unique ((fiberIsoClassFunctor p).obj (residue Λ k)) where
  default := fiberResidueClass p
  uniq := fiberResidueClass_spec p

/-- The associated isomorphism-class functor of a predeformation category is a
predeformation functor. -/
instance instIsPredeformationFunctor_fiberIsoClassFunctor [IsPredeformationCategory p] :
    IsPredeformationFunctor (fiberIsoClassFunctor p) where
  unique_residue := ⟨inferInstance⟩

/-- Matching pair of tangent vectors over the dual-number pullback, using that both
map to the unique residue class. -/
def fiberDualTangentAddPair [IsPredeformationCategory p]
    (x y : (fiberIsoClassFunctor p).obj (dualNumber Λ k)) :
    Types.PullbackObj
      ((fiberIsoClassFunctor p).map (toResidue (dualNumber Λ k)))
      ((fiberIsoClassFunctor p).map (dualNumberToResidue Λ k)) :=
  ⟨(x, y), Subsingleton.elim _ _⟩

/-- Addition on `F-bar(k[ε])` via the (H2) comparison along `k[ε] ×_k k[ε]` and the sum map. -/
def addFiberDualTangent [IsPredeformationCategory p]
    [HasSchlessingerH2 (fiberIsoClassFunctor p)]
    (x y : (fiberIsoClassFunctor p).obj (dualNumber Λ k)) :
    (fiberIsoClassFunctor p).obj (dualNumber Λ k) :=
  (fiberIsoClassFunctor p).map dualNumberSum
    ((Equiv.ofBijective
        (pullbackObjMap_subtype (fiberIsoClassFunctor p)
          (dualNumberPullbackFst (dualNumber Λ k))
          (dualNumberPullbackSnd (dualNumber Λ k))
          (toResidue (dualNumber Λ k))
          (dualNumberToResidue Λ k)
          (isPullback_dualNumberPullback (dualNumber Λ k)))
        (HasSchlessingerH2.bijective_pullbackObjMap
          (toResidue (dualNumber Λ k))
          (dualNumberPullbackFst (dualNumber Λ k))
          (dualNumberPullbackSnd (dualNumber Λ k))
          (isPullback_dualNumberPullback (dualNumber Λ k)))).symm
      (fiberDualTangentAddPair p x y))

/-- Scalar multiplication on `F-bar(k[ε])` by dual-number scaling of `ε`. -/
def smulFiberDualTangent [IsPredeformationCategory p]
    (r : k) (x : (fiberIsoClassFunctor p).obj (dualNumber Λ k)) :
    (fiberIsoClassFunctor p).obj (dualNumber Λ k) :=
  (fiberIsoClassFunctor p).map (dualNumberScaleHom Λ r) x

/-- Zero of `F-bar(k[ε])`, as the image of the unique residue class along `k ⟶ k[ε]`. -/
def zeroFiberDualTangent [IsPredeformationCategory p] :
    (fiberIsoClassFunctor p).obj (dualNumber Λ k) :=
  (fiberIsoClassFunctor p).map (residueToDualNumber Λ k) (fiberResidueClass p)

/-- Addition on `F-bar(k[ε])`. -/
instance instAdd_fiberDualTangent [IsPredeformationCategory p]
    [HasSchlessingerH2 (fiberIsoClassFunctor p)] :
    Add ((fiberIsoClassFunctor p).obj (dualNumber Λ k)) where
  add := addFiberDualTangent p

/-- Zero on `F-bar(k[ε])`. -/
instance instZero_fiberDualTangent [IsPredeformationCategory p] :
    Zero ((fiberIsoClassFunctor p).obj (dualNumber Λ k)) where
  zero := zeroFiberDualTangent p

/-- Negation on `F-bar(k[ε])`, as scaling by `-1`. -/
instance instNeg_fiberDualTangent [IsPredeformationCategory p] :
    Neg ((fiberIsoClassFunctor p).obj (dualNumber Λ k)) where
  neg x := smulFiberDualTangent p (-1) x

/-- Scalar multiplication on `F-bar(k[ε])`. -/
instance instSMul_fiberDualTangent [IsPredeformationCategory p] :
    SMul k ((fiberIsoClassFunctor p).obj (dualNumber Λ k)) where
  smul := smulFiberDualTangent p

/-- The additive group structure on `F-bar(k[ε])`. -/
instance instAddCommGroup_fiberDualTangent [IsPredeformationCategory p]
    [HasSchlessingerH2 (fiberIsoClassFunctor p)] :
    AddCommGroup ((fiberIsoClassFunctor p).obj (dualNumber Λ k)) := by
  have laws :
      (∀ left middle right : (fiberIsoClassFunctor p).obj (dualNumber Λ k), left + middle + right = left + (middle + right)) ∧
      (∀ value : (fiberIsoClassFunctor p).obj (dualNumber Λ k), 0 + value = value) ∧
      (∀ value : (fiberIsoClassFunctor p).obj (dualNumber Λ k), value + 0 = value) ∧
      (∀ value : (fiberIsoClassFunctor p).obj (dualNumber Λ k), -value + value = 0) ∧
      (∀ left right : (fiberIsoClassFunctor p).obj (dualNumber Λ k), left + right = right + left) := sorry
  exact { add_assoc := laws.1
          zero_add := laws.2.1
          add_zero := laws.2.2.1
          nsmul := nsmulRec
          neg_add_cancel := laws.2.2.2.1
          zsmul := zsmulRec
          add_comm := laws.2.2.2.2 }

/-- The `k`-module structure on `F-bar(k[ε])`. -/
instance instModule_fiberDualTangent [IsPredeformationCategory p]
    [HasSchlessingerH2 (fiberIsoClassFunctor p)] :
    Module k ((fiberIsoClassFunctor p).obj (dualNumber Λ k)) := by
  have laws :
      (∀ value : (fiberIsoClassFunctor p).obj (dualNumber Λ k), (1 : k) • value = value) ∧
      (∀ left right : k, ∀ value : (fiberIsoClassFunctor p).obj (dualNumber Λ k), (left * right) • value = left • (right • value)) ∧
      (∀ scalar : k, scalar • (0 : (fiberIsoClassFunctor p).obj (dualNumber Λ k)) = 0) ∧
      (∀ scalar : k, ∀ left right : (fiberIsoClassFunctor p).obj (dualNumber Λ k), scalar • (left + right) = scalar • left + scalar • right) ∧
      (∀ left right : k, ∀ value : (fiberIsoClassFunctor p).obj (dualNumber Λ k), (left + right) • value = left • value + right • value) ∧
      (∀ value : (fiberIsoClassFunctor p).obj (dualNumber Λ k), (0 : k) • value = 0) := sorry
  exact { one_smul := laws.1
          mul_smul := laws.2.1
          smul_zero := laws.2.2.1
          smul_add := laws.2.2.2.1
          add_smul := laws.2.2.2.2.1
          zero_smul := laws.2.2.2.2.2 }

variable (G : ArtinianLocalAlgCat Λ k ⥤ Type v)

/-- The unique value of a predeformation functor at the residue field. -/
def residuePoint [IsPredeformationFunctor G] : G.obj (residue Λ k) := by
  have existence : ∃! point : G.obj (residue Λ k), ∀ value, value = point := by
    obtain ⟨singleton⟩ := IsPredeformationFunctor.unique_residue (F := G)
    exact ⟨singleton.default, singleton.uniq, fun point property ↦
      (property singleton.default).symm⟩
  exact existence.choose

/-- Every value of a predeformation functor at the residue field equals its residue point. -/
theorem residuePoint_spec [IsPredeformationFunctor G] (value : G.obj (residue Λ k)) :
    value = residuePoint G := by
  obtain ⟨singleton⟩ := IsPredeformationFunctor.unique_residue (F := G)
  exact (singleton.uniq value).trans (singleton.uniq (residuePoint G)).symm

/-- The residue value is the singleton with its uniquely specified residue point. -/
instance instUnique_obj_residue [IsPredeformationFunctor G] :
    Unique (G.obj (residue Λ k)) where
  default := residuePoint G
  uniq := residuePoint_spec G

/-- Matching pair of values over `A ×_k k[V]`, using uniqueness at the residue field. -/
def objSquareZeroAddPair [IsPredeformationFunctor G] [HasSchlessingerH2 G]
    {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (x y : G.obj (squareZero Λ k V)) :
    Types.PullbackObj
      (G.map (toResidue (squareZero Λ k V)))
      (G.map (squareZeroToResidue Λ k V)) :=
  ⟨(x, y), Subsingleton.elim _ _⟩

/-- The inverse square-zero pullback comparison, constructed by adding finite basis coordinates
through the dual-number comparisons supplied by Schlessinger's condition (H2). -/
def squareZeroPullbackInverse [IsPredeformationFunctor G] [HasSchlessingerH2 G]
    (A : ArtinianLocalAlgCat Λ k) (V : Type u)
    [AddCommGroup V] [Module k V] [Module.Finite k V] :
    Types.PullbackObj (G.map (toResidue A)) (G.map (squareZeroToResidue Λ k V)) →
      G.obj (squareZeroPullback A V) := by
  classical
  let target := squareZeroPullback A V
  let source := dualNumberPullback target
  have matching : ∀ value : source.carrier, value.val.1.val.2.fst = value.val.2.fst := by
    intro value
    have first := value.val.1.property
    have second := value.property
    change (toResidue A).hom value.val.1.val.1 = value.val.1.val.2.fst at first
    change (toResidue A).hom value.val.1.val.1 = value.val.2.fst at second
    exact first.symm.trans second
  let shift := fun vector : V ↦
    let translate : source.carrier → target.carrier := fun value ↦
      ⟨(value.val.1.val.1,
        ⟨value.val.1.val.2.fst, value.val.1.val.2.snd + value.val.2.snd • vector⟩),
        value.val.1.property⟩
    let hom : source.carrier →ₐ[Λ] target.carrier :=
      { toFun := translate
        map_one' := by
          apply Subtype.ext
          apply Prod.ext
          · rfl
          · apply TrivSqZeroExt.ext
            · change (1 : k) = 1
              rfl
            · change (0 : V) + (0 : k) • vector = 0
              simp
        map_mul' := by
          intro left right
          apply Subtype.ext
          apply Prod.ext
          · rfl
          · apply TrivSqZeroExt.ext
            · rfl
            · change
                (left.val.1.val.2.fst • right.val.1.val.2.snd +
                    MulOpposite.op right.val.1.val.2.fst • left.val.1.val.2.snd) +
                  (left.val.2.fst • right.val.2.snd +
                    MulOpposite.op right.val.2.fst • left.val.2.snd) • vector =
                left.val.1.val.2.fst • (right.val.1.val.2.snd + right.val.2.snd • vector) +
                  MulOpposite.op right.val.1.val.2.fst •
                    (left.val.1.val.2.snd + left.val.2.snd • vector)
              simp only [op_smul_eq_smul, smul_eq_mul, smul_add, add_smul, smul_smul]
              rw [matching left, matching right]
              abel
        map_zero' := by
          apply Subtype.ext
          apply Prod.ext
          · rfl
          · apply TrivSqZeroExt.ext
            · change (0 : k) = 0
              rfl
            · change (0 : V) + (0 : k) • vector = 0
              simp
        map_add' := by
          intro left right
          apply Subtype.ext
          apply Prod.ext
          · rfl
          · apply TrivSqZeroExt.ext
            · rfl
            · change
                (left.val.1.val.2.snd + right.val.1.val.2.snd) +
                    (left.val.2.snd + right.val.2.snd) • vector =
                  (left.val.1.val.2.snd + left.val.2.snd • vector) +
                    (right.val.1.val.2.snd + right.val.2.snd • vector)
              simp only [add_smul]
              abel
        commutes' := by
          intro scalar
          apply Subtype.ext
          apply Prod.ext
          · rfl
          · apply TrivSqZeroExt.ext
            · rfl
            · change (0 : V) + (0 : k) • vector = 0
              simp }
    have localness : IsLocalHom hom := by
      constructor
      intro value unit
      have coefficientUnit : IsUnit value.val.1.val.1 :=
        unit.map (squareZeroPullbackFst A V).hom
      have firstUnit : IsUnit value.val.1 :=
        isUnit_of_map_unit (squareZeroPullbackFst A V).hom value.val.1 coefficientUnit
      exact isUnit_of_map_unit (dualNumberPullbackFst target).hom value firstUnit
    have compatibility : residueCompat hom localness = residueIsoHom source := by
      apply AlgHom.ext
      intro residueClass
      induction residueClass using Quotient.inductionOn with
      | h value => rfl
    Hom.of hom localness compatibility
  let basis := Module.finBasis k V
  intro pair
  let update := fun (current : G.obj target) (index : Fin (Module.finrank k V)) ↦
    let tangent := G.map
      (squareZeroMap (basis.coord index) ≫ (dualNumberIsoSquareZero Λ k).inv) pair.val.2
    let compatible : Types.PullbackObj
        (G.map (toResidue target)) (G.map (dualNumberToResidue Λ k)) :=
      ⟨(current, tangent), Subsingleton.elim _ _⟩
    G.map (shift (basis index))
      ((Equiv.ofBijective
        (pullbackObjMap_subtype G (dualNumberPullbackFst target) (dualNumberPullbackSnd target)
          (toResidue target) (dualNumberToResidue Λ k) (isPullback_dualNumberPullback target))
        (HasSchlessingerH2.bijective_pullbackObjMap
          (toResidue target) (dualNumberPullbackFst target) (dualNumberPullbackSnd target)
          (isPullback_dualNumberPullback target))).symm compatible)
  exact (List.finRange (Module.finrank k V)).foldl update
    (G.map (squareZeroPullbackSection A V) pair.val.1)

/-- The finite-coordinate reconstruction is a two-sided inverse of the square-zero comparison. -/
theorem squareZeroPullbackInverse_spec [IsPredeformationFunctor G] [HasSchlessingerH2 G]
    (A : ArtinianLocalAlgCat Λ k) (V : Type u)
    [AddCommGroup V] [Module k V] [Module.Finite k V] :
    Function.LeftInverse (squareZeroPullbackInverse G A V)
      (pullbackObjMap_subtype G (squareZeroPullbackFst A V) (squareZeroPullbackSnd A V)
        (toResidue A) (squareZeroToResidue Λ k V) (isPullback_squareZeroPullback A V)) ∧
    Function.RightInverse (squareZeroPullbackInverse G A V)
      (pullbackObjMap_subtype G (squareZeroPullbackFst A V) (squareZeroPullbackSnd A V)
        (toResidue A) (squareZeroToResidue Λ k V) (isPullback_squareZeroPullback A V)) := sorry

/-- Addition on `G.obj (squareZero Λ k V)` via (H2) along `k[V] ×_k k[V]`. -/
def addObjSquareZero [IsPredeformationFunctor G] [HasSchlessingerH2 G]
    {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (x y : G.obj (squareZero Λ k V)) : G.obj (squareZero Λ k V) :=
  G.map (squareZeroSum V)
    (squareZeroPullbackInverse G (squareZero Λ k V) V (objSquareZeroAddPair G x y))

/-- Scalar multiplication on `G.obj (squareZero Λ k V)`. -/
def smulObjSquareZero {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (r : k) (x : G.obj (squareZero Λ k V)) : G.obj (squareZero Λ k V) :=
  G.map (squareZeroMap (LinearMap.lsmul k V r)) x

/-- Zero of `G.obj (squareZero Λ k V)`. -/
def zeroObjSquareZero [IsPredeformationFunctor G]
    {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V] :
    G.obj (squareZero Λ k V) :=
  G.map (residueToSquareZero V) (residuePoint G)

/-- Addition on values at `k[V]`. -/
instance instAdd_obj_squareZero [IsPredeformationFunctor G] [HasSchlessingerH2 G]
    (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V] :
    Add (G.obj (squareZero Λ k V)) where
  add := addObjSquareZero G

/-- Zero on values at `k[V]`. -/
instance instZero_obj_squareZero [IsPredeformationFunctor G]
    (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V] :
    Zero (G.obj (squareZero Λ k V)) where
  zero := zeroObjSquareZero G

/-- Negation on values at `k[V]`. -/
instance instNeg_obj_squareZero [IsPredeformationFunctor G]
    (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V] :
    Neg (G.obj (squareZero Λ k V)) where
  neg x := smulObjSquareZero G (-1) x

/-- Scalar multiplication on values at `k[V]`. -/
instance instSMul_obj_squareZero (V : Type u) [AddCommGroup V] [Module k V]
    [Module.Finite k V] : SMul k (G.obj (squareZero Λ k V)) where
  smul := smulObjSquareZero G

/-- The additive group structure on `G(k[V])`. -/
instance instAddCommGroup_obj_squareZero [IsPredeformationFunctor G] [HasSchlessingerH2 G]
    (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V] :
    AddCommGroup (G.obj (squareZero Λ k V)) := by
  have laws :
      (∀ left middle right : G.obj (squareZero Λ k V), left + middle + right = left + (middle + right)) ∧
      (∀ value : G.obj (squareZero Λ k V), 0 + value = value) ∧
      (∀ value : G.obj (squareZero Λ k V), value + 0 = value) ∧
      (∀ value : G.obj (squareZero Λ k V), -value + value = 0) ∧
      (∀ left right : G.obj (squareZero Λ k V), left + right = right + left) := sorry
  exact { add_assoc := laws.1
          zero_add := laws.2.1
          add_zero := laws.2.2.1
          nsmul := nsmulRec
          neg_add_cancel := laws.2.2.2.1
          zsmul := zsmulRec
          add_comm := laws.2.2.2.2 }

/-- The `k`-module structure on `G(k[V])`. -/
instance instModule_obj_squareZero [IsPredeformationFunctor G] [HasSchlessingerH2 G]
    (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V] :
    Module k (G.obj (squareZero Λ k V)) := by
  have laws :
      (∀ value : G.obj (squareZero Λ k V), (1 : k) • value = value) ∧
      (∀ left right : k, ∀ value : G.obj (squareZero Λ k V), (left * right) • value = left • (right • value)) ∧
      (∀ scalar : k, scalar • (0 : G.obj (squareZero Λ k V)) = 0) ∧
      (∀ scalar : k, ∀ left right : G.obj (squareZero Λ k V), scalar • (left + right) = scalar • left + scalar • right) ∧
      (∀ left right : k, ∀ value : G.obj (squareZero Λ k V), (left + right) • value = left • value + right • value) ∧
      (∀ value : G.obj (squareZero Λ k V), (0 : k) • value = 0) := sorry
  exact { one_smul := laws.1
          mul_smul := laws.2.1
          smul_zero := laws.2.2.1
          smul_add := laws.2.2.2.1
          add_smul := laws.2.2.2.2.1
          zero_smul := laws.2.2.2.2.2 }

/-- Transport of tangent vectors along `k[ε] ≅ k[k]`. -/
def fiberDualTangentEquiv_squareZero [IsPredeformationCategory p] :
    (fiberIsoClassFunctor p).obj (dualNumber Λ k) ≃
      (squareZeroEval (fiberIsoClassFunctor p)).obj (of k k) := by
  let forward := (fiberIsoClassFunctor p).map (dualNumberIsoSquareZero Λ k).hom
  let backward := (fiberIsoClassFunctor p).map (dualNumberIsoSquareZero Λ k).inv
  have laws : Function.LeftInverse backward forward ∧
      Function.RightInverse backward forward := sorry
  exact { toFun := forward, invFun := backward, left_inv := laws.1, right_inv := laws.2 }

variable [IsPredeformationCategory p] [HasSchlessingerH2 (fiberIsoClassFunctor p)]
variable (V : FGModuleCat.{u} k)

/-- The bilinear map `(x, v) ↦ F-bar(k[span{v}])(x)` underlying the tensor comparison. -/
def fiberDualTangentTensorBilin :
    (fiberIsoClassFunctor p).obj (dualNumber Λ k) →ₗ[k]
      V →ₗ[k] (fiberIsoClassFunctor p).obj (squareZero Λ k V) := by
  let comparison := fun (tangent : (fiberIsoClassFunctor p).obj (dualNumber Λ k)) (vector : V) ↦
    (fiberIsoClassFunctor p).map
      ((dualNumberIsoSquareZero Λ k).hom ≫
        squareZeroMap (LinearMap.toSpanSingleton k V vector)) tangent
  have laws :
      (∀ left right vector, comparison (left + right) vector = comparison left vector + comparison right vector) ∧
      (∀ (scalar : k) tangent vector,
        comparison (scalar • tangent) vector = scalar • comparison tangent vector) ∧
      (∀ tangent left right, comparison tangent (left + right) = comparison tangent left + comparison tangent right) ∧
      (∀ (scalar : k) tangent vector,
        comparison tangent (scalar • vector) = scalar • comparison tangent vector) := sorry
  exact LinearMap.mk₂ k comparison laws.1 laws.2.1 laws.2.2.1 laws.2.2.2

/-- The canonical `k`-linear comparison `F-bar(k[ε]) ⊗[k] V →ₗ[k] F-bar(k[V])`. -/
def fiberDualTangentTensor :
    (fiberIsoClassFunctor p).obj (dualNumber Λ k) ⊗[k] V →ₗ[k]
      (fiberIsoClassFunctor p).obj (squareZero Λ k V) :=
  TensorProduct.lift (fiberDualTangentTensorBilin p V)

/-- On pure tensors, `fiberDualTangentTensor` sends `x ⊗ₜ v` to the image of `x` under
the map induced by `spanSingleton v`. -/
theorem fiberDualTangentTensor_tmul
    (x : (fiberIsoClassFunctor p).obj (dualNumber Λ k)) (v : V) :
    fiberDualTangentTensor p V (x ⊗ₜ v) =
      (fiberIsoClassFunctor p).map
        ((dualNumberIsoSquareZero Λ k).hom ≫
          squareZeroMap (LinearMap.toSpanSingleton k V v)) x := sorry

/-- `fiberDualTangentTensor` is the lift of `fiberDualTangentTensorBilin`. -/
theorem fiberDualTangentTensor_spec :
    fiberDualTangentTensor p V = TensorProduct.lift (fiberDualTangentTensorBilin p V) := sorry

/-- Type-level form of `fiberDualTangentTensor`, for a finite `k`-module `W`. -/
def fiberDualTangentTensor_of (W : Type u) [AddCommGroup W] [Module k W] [Module.Finite k W] :
    (fiberIsoClassFunctor p).obj (dualNumber Λ k) ⊗[k] W →ₗ[k]
      (fiberIsoClassFunctor p).obj (squareZero Λ k W) :=
  fiberDualTangentTensor p (of k W)

/-- `fiberDualTangentTensor_of` is `fiberDualTangentTensor` at `FGModuleCat.of k W`. -/
theorem fiberDualTangentTensor_of_eq (W : Type u) [AddCommGroup W] [Module k W]
    [Module.Finite k W] :
    fiberDualTangentTensor_of p W = fiberDualTangentTensor p (of k W) := sorry

/-- The comparison `F-bar(k[ε]) ⊗[k] V → F-bar(k[V])` is natural in the finite-dimensional
`k`-vector space `V`. -/
theorem fiberDualTangentTensor_naturality {W : FGModuleCat.{u} k} (f : V ⟶ W)
    (x : (fiberIsoClassFunctor p).obj (dualNumber Λ k) ⊗[k] V) :
    (fiberIsoClassFunctor p).map ((squareZeroFunctor Λ k).map f)
        (fiberDualTangentTensor p V x) =
      fiberDualTangentTensor p W (TensorProduct.map LinearMap.id f.hom.hom x) := sorry

/-- The canonical tangent tensor comparison is bijective for every finite-dimensional vector space. -/
theorem bijective_fiberDualTangentTensor :
    Function.Bijective (fiberDualTangentTensor p V) := sorry

end CategoryTheory.Functor
