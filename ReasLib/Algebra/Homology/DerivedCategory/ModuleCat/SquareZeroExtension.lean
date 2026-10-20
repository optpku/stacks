module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Additive
public import ReasLib.Algebra.Category.ModuleCat.Free.Adjunction
public import ReasLib.Algebra.Category.ModuleCat.Graded.Colimits
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor.ChangeOfRings
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.FixedRight
public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Bifunctor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Bifunctor
public import ReasLib.Algebra.Category.ModuleCat.SquareZeroExtension.Kernel
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Bounded
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor.CellModel
public import ReasLib.Algebra.Homology.CochainComplex.KFlat.ModuleCat.BoundedAbove
import Mathlib.Tactic.CrossRefAttribute

/-!
# Canonical obstruction class of a bounded-above derived module

Along a square-zero surjection `f : R' →+* R` with kernel `I`, every `K` in `D⁻(R)` has a
canonical morphism `ω(K) : K ⟶ K ⊗[R]^L I[2]` in `D(R)`, obtained from a bounded-above
termwise-free replacement by lifting matrix coefficients of the differentials along `f` and
factoring `d' ∘ d'` through `I`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open DerivedCategory
open HomologicalComplex
open scoped DerivedTensorProduct
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace ModuleCat.SquareZeroExtension

variable {R' R : Type u} [CommRing R'] [CommRing R]

/-- The coefficientwise lift of an element of `R` along a square-zero surjection, sending `0` to
`0`. -/
private def liftCoeff (f : R' →+* R) [f.IsSquareZeroExtension] (r : R) : R' :=
  have := Classical.decEq R
  if r = 0 then 0
  else Function.surjInv (RingHom.IsSquareZeroExtension.surjective (f := f)) r

/-- `liftCoeff` preserves zero. -/
private theorem liftCoeff_zero (f : R' →+* R) [f.IsSquareZeroExtension] :
    liftCoeff f 0 = 0 := by
  classical
  simp [liftCoeff]

/-- `liftCoeff` is a section of the square-zero surjection. -/
private theorem liftCoeff_spec (f : R' →+* R) [f.IsSquareZeroExtension] (r : R) :
    f (liftCoeff f r) = r := sorry

/-- Restrict a coefficient in `R'` to the kernel of a square-zero surjection, sending
non-kernel coefficients to `0`. -/
private def coeffToKer (f : R' →+* R) [f.IsSquareZeroExtension] (r : R') : RingHom.ker f :=
  have := Classical.decEq R
  if h : f r = 0 then ⟨r, h⟩ else 0

/-- `coeffToKer` preserves zero. -/
private theorem coeffToKer_zero (f : R' →+* R) [f.IsSquareZeroExtension] :
    coeffToKer f 0 = 0 := by
  classical
  apply Subtype.ext
  simp [coeffToKer]

/-- Lift an `R`-linear map of free modules along a square-zero surjection by lifting matrix
coefficients of the images of basis vectors. -/
private def liftFreeLinearMap (f : R' →+* R) [f.IsSquareZeroExtension] {ι κ : Type u}
    (φ : ModuleCat.Free.obj.{u, u} R ι ⟶ ModuleCat.Free.obj.{u, u} R κ) :
    ModuleCat.Free.obj.{u, u} R' ι ⟶ ModuleCat.Free.obj.{u, u} R' κ :=
  ModuleCat.ofHom
    (Finsupp.lift (κ →₀ R') R' ι fun i ↦
      Finsupp.mapRange (liftCoeff f)
        (have := Classical.decEq R; dif_pos (rfl : (0 : R) = 0))
        (φ.hom (Finsupp.single i (1 : R))))

/-- `liftFreeLinearMap` on a basis vector lifts the finitely supported matrix column of `φ`. -/
private theorem liftFreeLinearMap_single (f : R' →+* R) [f.IsSquareZeroExtension] {ι κ : Type u}
    (φ : ModuleCat.Free.obj.{u, u} R ι ⟶ ModuleCat.Free.obj.{u, u} R κ) (i : ι) :
    (liftFreeLinearMap f φ).hom (Finsupp.single i (1 : R')) =
      Finsupp.mapRange (liftCoeff f)
        (have := Classical.decEq R; dif_pos (rfl : (0 : R) = 0))
        (φ.hom (Finsupp.single i (1 : R))) := sorry

/-- The single complex `I[0]` associated to the kernel of a square-zero extension. -/
abbrev kernelSingle (f : R' →+* R) [f.IsSquareZeroExtension] :
    DerivedCategory (ModuleCat.{u} R) :=
  (singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj (kernelModule f)

/-- The cochain complex `I[0]` associated to the kernel of a square-zero extension. -/
private abbrev kernelSingleComplex (f : R' →+* R) [f.IsSquareZeroExtension] :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  (HomologicalComplex.single (ModuleCat.{u} R) (up ℤ) (0 : ℤ)).obj (kernelModule f)

/-- The shifted derived tensor `(K ⊗[R]^L I[0])⟦2⟧`. -/
abbrev tensorKernelShift (f : R' →+* R) [f.IsSquareZeroExtension]
    (K : DerivedCategory (ModuleCat.{u} R)) :
    DerivedCategory (ModuleCat.{u} R) :=
  (K ⊗[R]^L kernelSingle f)⟦(2 : ℤ)⟧

/-- The map `(α ⊗ id_{I[0]})⟦2⟧` induced by a morphism of derived modules. -/
def tensorKernelShiftMap (f : R' →+* R) [f.IsSquareZeroExtension]
    {K L : DerivedCategory (ModuleCat.{u} R)} (α : K ⟶ L) :
    tensorKernelShift f K ⟶ tensorKernelShift f L :=
  (shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (2 : ℤ)).map
    ((DerivedTensor.Right.functor (kernelSingle f)).map α)

/-- A chosen integer witnessing that a derived object is cohomologically bounded above. -/
private def isBoundedAboveBound (K : DerivedCategory (ModuleCat.{u} R))
    (hK : K.IsBoundedAbove) : ℤ :=
  Classical.choose hK

/-- The chosen cohomological upper bound bounds the object. -/
private instance instIsLE_isBoundedAboveBound (K : DerivedCategory (ModuleCat.{u} R))
    (hK : K.IsBoundedAbove) :
    K.IsLE (isBoundedAboveBound K hK) :=
  Classical.choose_spec hK

/-- A cochain preimage inherits the derived object's cohomological upper bound. -/
private instance instObjPreimage_isLE (K : DerivedCategory (ModuleCat.{u} R)) {n : ℤ}
    [K.IsLE n] :
    (DerivedCategory.Q.objPreimage K).IsLE n :=
  (DerivedCategory.isLE_Q_obj_iff (DerivedCategory.Q.objPreimage K) n).mp
    (DerivedCategory.TStructure.t.isLE_of_iso
      (DerivedCategory.Q.objObjPreimageIso K).symm n)

/-- A bounded-above cochain representative of a derived object, obtained by truncating a
chosen preimage. -/
private def boundedRepresentative (K : DerivedCategory (ModuleCat.{u} R))
    (hK : K.IsBoundedAbove) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  (DerivedCategory.Q.objPreimage K).truncLE (isBoundedAboveBound K hK)

/-- One degree of a bounded-above termwise-free replacement: free generators, the comparison
to the original complex, and the cochain differential as a map of free modules. -/
private abbrev FreeReplacementStage (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) (k : ℕ) :=
  Σ ι : Type u, Σ κ : Type u,
    (ModuleCat.Free.obj.{u, u} R ι ⟶ K.X (a + 1 - k)) ×
      (ModuleCat.Free.obj.{u, u} R ι ⟶ ModuleCat.Free.obj.{u, u} R κ)

/-- Degree identity used to compare `K.X a` with the `k = 1` stage target. -/
private theorem freeReplacement_stage1_deg (a : ℤ) : a = a + 1 - (1 : ℕ) := by omega

/-- Degree identity aligning the pullback target with the previous stage comparison. -/
private theorem freeReplacement_pullbackDeg (a : ℤ) (k : ℕ) :
    a + 1 - ((k + 1 : ℕ) : ℤ) = a - (k + 1 : ℕ) + 1 := by omega

/-- Degree identity aligning the new stage comparison with the pullback source. -/
private theorem freeReplacement_toKDeg (a : ℤ) (k : ℕ) :
    a - (k + 1 : ℕ) = a + 1 - ((k + 2 : ℕ) : ℤ) := by omega

/-- Construct the next lower free stage from the pullback of the original differential
against the comparison on the kernel of the previous stage's differential. -/
private def FreeReplacementStage.descend (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ)
    {k : ℕ} (prev : FreeReplacementStage K a (k + 1)) : FreeReplacementStage K a (k + 2) :=
  let i : ℤ := a - (k + 1 : ℕ)
  let kerToK := kernel.ι prev.2.2.2 ≫ prev.2.2.1 ≫
    eqToHom (congrArg K.X (freeReplacement_pullbackDeg a k))
  let W := pullback (K.d i (i + 1)) kerToK
  ⟨(W : Type u), prev.1,
    ModuleCat.Free.desc.{u, u} R (TypeCat.ofHom fun x : (W : Type u) ↦ x) ≫
      pullback.fst (K.d i (i + 1)) kerToK ≫
      eqToHom (congrArg K.X (freeReplacement_toKDeg a k)),
    ModuleCat.Free.desc.{u, u} R (TypeCat.ofHom fun x : (W : Type u) ↦ x) ≫
      pullback.snd (K.d i (i + 1)) kerToK ≫ kernel.ι prev.2.2.2⟩

/-- Termwise-free replacement data in offset `k` below the bound, constructed by descending
induction so that each differential lands in the kernel of the next. -/
private def freeReplacementStage (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    (k : ℕ) → FreeReplacementStage K a k
  | 0 =>
    ⟨PEmpty.{u + 1}, PEmpty.{u + 1}, 0, 0⟩
  | 1 =>
    ⟨(K.X a : Type u), PEmpty.{u + 1},
      ModuleCat.Free.desc.{u, u} R (TypeCat.ofHom fun x : (K.X a : Type u) ↦ x) ≫
        eqToHom (congrArg K.X (freeReplacement_stage1_deg a)), 0⟩
  | k + 2 =>
    FreeReplacementStage.descend K a (freeReplacementStage K a (k + 1))

/-- The `ℕ`-offset of cohomological degree `n` relative to the bound `a`. -/
private def freeReplacementOffset (a n : ℤ) : ℕ :=
  Int.toNat (a + 1 - n)

/-- Generating type of the termwise-free replacement in degree `n`. -/
private def freeReplacementGens (K : CochainComplex (ModuleCat.{u} R) ℤ) (a n : ℤ) : Type u :=
  (freeReplacementStage K a (freeReplacementOffset a n)).1

/-- The generating type one degree higher in the free replacement agrees with the generating
type of the next cohomological degree. -/
private theorem freeReplacement_gensHigher_eq (K : CochainComplex (ModuleCat.{u} R) ℤ) (a i j : ℤ)
    (hij : i + 1 = j) :
    (freeReplacementStage K a (freeReplacementOffset a i)).2.1 =
      freeReplacementGens K a j := sorry

/-- The bounded-above termwise-free cochain complex replacing `K`. -/
private def freeReplacement (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ where
  X n := ModuleCat.Free.obj.{u, u} R (freeReplacementGens K a n)
  d i j :=
    if hij : i + 1 = j then
      (freeReplacementStage K a (freeReplacementOffset a i)).2.2.2 ≫
        eqToHom (congrArg (fun ι : Type u ↦ ModuleCat.Free.obj.{u, u} R ι)
          (freeReplacement_gensHigher_eq K a i j hij))
    else 0
  shape i j hij := by
    exact dif_neg hij
  d_comp_d' i j k hij hjk := sorry

/-- The offset description of degree `n` recovers `n` after subtracting from `a + 1`,
provided `n ≤ a + 1`. -/
private theorem freeReplacement_degree_eq (a n : ℤ) (hn : n ≤ a + 1) :
    a + 1 - freeReplacementOffset a n = n := by
  simp only [freeReplacementOffset, Int.toNat_of_nonneg (by omega : 0 ≤ a + 1 - n)]
  omega

/-- Comparison from the termwise-free replacement to the original bounded-above complex.
In degrees `n > a + 1` both sides vanish, so the component is the zero map. -/
private def freeReplacementComparison (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ)
    [hbound : K.IsStrictlyLE a] :
    freeReplacement K a ⟶ K where
  f n :=
    if hn : n ≤ a + 1 then
      (freeReplacementStage K a (freeReplacementOffset a n)).2.2.1 ≫
        eqToHom (congrArg K.X (freeReplacement_degree_eq a n hn))
    else
      0
  comm' i j hij := sorry

/-- The free comparison is a quasi-isomorphism for a strictly bounded-above input. -/
private theorem quasiIso_freeReplacementComparison
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) [hbound : K.IsStrictlyLE a] :
    QuasiIso (freeReplacementComparison K a) := sorry

/-- Reverse the localization of the actual free comparison. -/
private def freeReplacementComparisonDerivedInv
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) [hbound : K.IsStrictlyLE a] :
    DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj (freeReplacement K a) :=
  (Localization.isoOfHom DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (up ℤ))
    (freeReplacementComparison K a) (quasiIso_freeReplacementComparison K a)).inv

/-- The displayed bounded-above termwise-free replacement is K-flat. -/
private theorem freeReplacement_isKFlat (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    (freeReplacement K a).IsKFlat := sorry

/-- Convert a finitely supported `ker f`-valued function into an elementary tensor. -/
private def finsuppKerToTensor (f : R' →+* R) [f.IsSquareZeroExtension] {ι : Type u}
    (x : ι →₀ RingHom.ker f) :
    TensorProduct R (ι →₀ R) (RingHom.ker f) :=
  x.sum fun a v ↦ TensorProduct.tmul R (Finsupp.single a (1 : R)) v

/-- The obstruction coefficients of `d' ∘ d'` on a generator of the free replacement. -/
private def omegaOnGens (f : R' →+* R) [f.IsSquareZeroExtension]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a i : ℤ)
    (x : freeReplacementGens K a i) :
    freeReplacementGens K a (i + 2) →₀ RingHom.ker f :=
  let h₁ := freeReplacement_gensHigher_eq K a i (i + 1) rfl
  let h₂ := freeReplacement_gensHigher_eq K a (i + 1) (i + 2)
      ((add_assoc i (1 : ℤ) 1).trans
        (congrArg (HAdd.hAdd i) (one_add_one_eq_two : (1 : ℤ) + 1 = 2)))
  let y :=
    (liftFreeLinearMap f
        (freeReplacementStage K a (freeReplacementOffset a i)).2.2.2).hom
      (Finsupp.single x (1 : R'))
  let y' := Finsupp.equivMapDomain (Equiv.cast h₁) y
  let z :=
    (liftFreeLinearMap f
        (freeReplacementStage K a (freeReplacementOffset a (i + 1))).2.2.2).hom y'
  Finsupp.mapRange (coeffToKer f)
    (have := Classical.decEq R; dif_pos (RingHom.map_zero f))
    (Finsupp.equivMapDomain (Equiv.cast h₂) z)

/-- The cochain-level component of `ω` on the free replacement, with values in the termwise
tensor `P^{i+2} ⊗ I`. -/
private def canonicalClassComponent (f : R' →+* R) [f.IsSquareZeroExtension]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a i : ℤ) :
    (freeReplacement K a).X i ⟶
      (freeReplacement K a).X (i + 2) ⊗ kernelModule f :=
  let component := fun x : (freeReplacement K a).X i ↦
    finsuppKerToTensor f
      (Finsupp.lift (freeReplacementGens K a (i + 2) →₀ RingHom.ker f) R
        (freeReplacementGens K a i) (fun g ↦ omegaOnGens f K a i g) x)
  have laws : (∀ x y, component (x + y) = component x + component y) ∧
      (∀ (r : R) x, component (r • x) = r • component x) := sorry
  ModuleCat.ofHom { toFun := component, map_add' := laws.1, map_smul' := laws.2 }

/-- Termwise tensor of a cochain complex with the square-zero kernel. -/
private abbrev tensorKernelComplex (f : R' →+* R) [f.IsSquareZeroExtension]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  K ⊗ kernelSingleComplex f

/-- The cochain map `P^• ⟶ (P^• ⊗ I[0])⟦2⟧` presenting `ω` on a termwise-free replacement. -/
private def canonicalClass_ofFree (f : R' →+* R) [f.IsSquareZeroExtension]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    freeReplacement K a ⟶ (tensorKernelComplex f (freeReplacement K a))⟦(2 : ℤ)⟧ where
  f i :=
    canonicalClassComponent f K a i ≫
      ιTensorObj (freeReplacement K a) (kernelSingleComplex f)
        (i + 2) 0 (i + 2) (add_zero (i + 2))
  comm' _ _ _ := sorry

/-- The tensor counit computes derived tensor on the displayed free replacement. -/
private def termwiseTensorComparisonIso (f : R' →+* R) [f.IsSquareZeroExtension]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    DerivedTensor.Bifunctor.obj (DerivedCategory.Q.obj (freeReplacement K a))
        (DerivedCategory.Q.obj (kernelSingleComplex f)) ≅
      DerivedCategory.Q.obj (tensorKernelComplex f (freeReplacement K a)) :=
  ModuleCat.DerivedTensorCellModel.counitIsoOfKFlatLeft
    (freeReplacement K a) (kernelSingleComplex f) (freeReplacement_isKFlat K a)

/-- The canonical tensor counit on the displayed free replacement is invertible. -/
private instance instIsIso_counitAppOfQ_kernelSingle (f : R' →+* R) [f.IsSquareZeroExtension]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    IsIso (DerivedTensor.Bifunctor.counitAppOfQ
      (freeReplacement K a) (kernelSingleComplex f)) :=
  (termwiseTensorComparisonIso f K a).isIso_hom

/-- Compare ordinary tensor on the displayed free replacement with fixed-right derived tensor. -/
private def termwiseToDerivedTensor (f : R' →+* R) [f.IsSquareZeroExtension]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    DerivedCategory.Q.obj (tensorKernelComplex f (freeReplacement K a)) ⟶
      DerivedCategory.Q.obj (freeReplacement K a) ⊗[R]^L kernelSingle f :=
  (termwiseTensorComparisonIso f K a).inv ≫
    (DerivedTensor.Bifunctor.Right.isoApp (kernelSingle f)
      (DerivedCategory.Q.obj (freeReplacement K a))).inv

/-- Reverse the localized truncation comparison using its cohomological upper bound. -/
private def ιTruncLEDerivedInv (K : DerivedCategory (ModuleCat.{u} R)) (hK : K.IsBoundedAbove) :
    DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage K) ⟶
      DerivedCategory.Q.obj (boundedRepresentative K hK) :=
  (Localization.isoOfHom DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (up ℤ))
    ((DerivedCategory.Q.objPreimage K).ιTruncLE (isBoundedAboveBound K hK))
    ((CochainComplex.quasiIso_ιTruncLE_iff _ _).mpr inferInstance)).inv

-- The public map uses private cochain machinery only in its implementation.
/-- The canonical morphism `ω(K) : K ⟶ K ⊗[R]^L I[2]` in `D(R)`. -/
@[no_expose] def canonicalClass (f : R' →+* R) [f.IsSquareZeroExtension]
    (K : DerivedCategory (ModuleCat.{u} R)) (hK : K.IsBoundedAbove) :
    K ⟶ tensorKernelShift f K :=
  let a := isBoundedAboveBound K hK
  have hbound : (boundedRepresentative K hK).IsStrictlyLE a := by
    dsimp [boundedRepresentative, a]
    infer_instance
  let P := freeReplacement (boundedRepresentative K hK) a
  (DerivedCategory.Q.objObjPreimageIso K).inv ≫
    ιTruncLEDerivedInv K hK ≫
    freeReplacementComparisonDerivedInv (boundedRepresentative K hK) a (hbound := hbound) ≫
    DerivedCategory.Q.map (canonicalClass_ofFree f (boundedRepresentative K hK) a) ≫
      (DerivedCategory.Q.commShiftIso (2 : ℤ)).hom.app
        (tensorKernelComplex f P) ≫
      ((shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (2 : ℤ)).map
        (termwiseToDerivedTensor f (boundedRepresentative K hK) a)) ≫
      ((shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (2 : ℤ)).map
        ((DerivedTensor.Right.functor (kernelSingle f)).map
          (DerivedCategory.Q.map
              (freeReplacementComparison (boundedRepresentative K hK) a (hbound := hbound)) ≫
            DerivedCategory.Q.map
              ((DerivedCategory.Q.objPreimage K).ιTruncLE a) ≫
            (DerivedCategory.Q.objObjPreimageIso K).hom)))

/-- The adjunct of `kernelToBaseChange` along extension of scalars `R → S`. -/
def kernelBaseChangeModule (f : R' →+* R) [f.IsSquareZeroExtension]
    {S' : Type u} [CommRing S'] (g : R' →+* S') :
    (ModuleCat.extendScalars (tensorCodomainIncludeRight f g)).obj (kernelModule f) ⟶
      kernelModule (tensorCodomainRingHom f g) :=
  ((ModuleCat.extendRestrictScalarsAdj (tensorCodomainIncludeRight f g)).homEquiv
      (kernelModule f) (kernelModule (tensorCodomainRingHom f g))).symm
    (ModuleCat.ofHom (X := kernelModule f)
      (Y := (ModuleCat.restrictScalars (tensorCodomainIncludeRight f g)).obj
        (kernelModule (tensorCodomainRingHom f g)))
      { toFun := fun i ↦ kernelToBaseChange f g i
        map_add' := (kernelToBaseChange f g).map_add
        map_smul' := sorry })

/-- On elementary tensors the adjunct kernel comparison is scalar multiplication of the
image of the kernel element. -/
theorem kernelBaseChangeModule_spec (f : R' →+* R) [f.IsSquareZeroExtension]
    {S' : Type u} [CommRing S'] (g : R' →+* S')
    (s : tensorCodomain f g) (i : RingHom.ker f) :
    (kernelBaseChangeModule f g).hom (s ⊗ₜ[R] i) =
      s • kernelToBaseChange f g i := sorry

-- The public comparison uses the private degree-zero cochain presentation in its body.
/-- The derived comparison `I[0] ⊗[R]^L S ⟶ J[0]` induced by `kernelBaseChange`. -/
@[no_expose] def kernelBaseChangeDerivedRight (f : R' →+* R) [f.IsSquareZeroExtension]
    {S' : Type u} [CommRing S'] (g : R' →+* S') :
    (ModuleCat.derivedExtensionOfScalars (tensorCodomainIncludeRight f g)).obj
        (kernelSingle f) ⟶
      kernelSingle (tensorCodomainRingHom f g) :=
  (Functor.LeftDerived.Homotopy.cochainCounit
      (ModuleCat.extendScalars (tensorCodomainIncludeRight f g))).app
      (kernelSingleComplex f) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
          (ModuleCat.extendScalars (tensorCodomainIncludeRight f g))
          (up ℤ) (0 : ℤ)).hom.app (kernelModule f)) ≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} (tensorCodomain f g)) (0 : ℤ)).map
      (kernelBaseChangeModule f g)

/-- Comparison `(K ⊗[R]^L I[2]) ⊗[R]^L S ⟶ (K ⊗[R]^L S) ⊗[S]^L J[2]` induced by
`kernelBaseChange`. -/
def kernelBaseChangeDerived (f : R' →+* R) [f.IsSquareZeroExtension]
    {S' : Type u} [CommRing S'] (g : R' →+* S')
    (K : DerivedCategory (ModuleCat.{u} R)) :
    ((ModuleCat.derivedExtensionOfScalars (tensorCodomainIncludeRight f g)).obj
        (tensorKernelShift f K)) ⟶
      tensorKernelShift (tensorCodomainRingHom f g)
        ((ModuleCat.derivedExtensionOfScalars (tensorCodomainIncludeRight f g)).obj K) :=
  (Functor.commShiftIso
      (ModuleCat.derivedExtensionOfScalars (tensorCodomainIncludeRight f g))
      (2 : ℤ)).hom.app (K ⊗[R]^L kernelSingle f) ≫
    (shiftFunctor (DerivedCategory (ModuleCat.{u} (tensorCodomain f g))) (2 : ℤ)).map
      ((ModuleCat.DerivedExtension.Tensor.FixedRight.comparisonIso
          (tensorCodomainIncludeRight f g) (kernelSingle f)).hom.app K ≫
        (derivedTensorChangeOfRingsMap (tensorCodomainIncludeRight f g)
            (kernelBaseChangeDerivedRight f g)).app K)

/-- The obstruction vanishes exactly when the derived object lifts across the square-zero extension. -/
theorem canonicalClass_eq_zero_iff (f : R' →+* R) [f.IsSquareZeroExtension]
    (K : DerivedCategory (ModuleCat.{u} R)) (hK : K.IsBoundedAbove) :
    canonicalClass f K hK = 0 ↔
      ∃ K' : DerivedCategory (ModuleCat.{u} R'),
        IsIsomorphic ((ModuleCat.derivedExtensionOfScalars f).obj K') K := sorry

/-- The obstruction is natural in morphisms between bounded-above derived modules. -/
theorem canonicalClass_natural (f : R' →+* R) [f.IsSquareZeroExtension]
    {K L : DerivedCategory (ModuleCat.{u} R)}
    (hK : K.IsBoundedAbove) (hL : L.IsBoundedAbove) (α : K ⟶ L) :
    canonicalClass f K hK ≫ tensorKernelShiftMap f α =
      α ≫ canonicalClass f L hL := sorry

variable {S' : Type u} [CommRing S']

/-- The obstruction commutes with arbitrary ring base change through the induced kernel map. -/
theorem canonicalClass_baseChange (f : R' →+* R) [f.IsSquareZeroExtension]
    (g : R' →+* S') (K : DerivedCategory (ModuleCat.{u} R))
    (hK : K.IsBoundedAbove) :
    (ModuleCat.derivedExtensionOfScalars (tensorCodomainIncludeRight f g)).map
          (canonicalClass f K hK) ≫
        kernelBaseChangeDerived f g K =
      canonicalClass (tensorCodomainRingHom f g)
        ((ModuleCat.derivedExtensionOfScalars (tensorCodomainIncludeRight f g)).obj K)
        (CategoryTheory.ModuleCat.derivedExtensionOfScalars_isBoundedAbove
          (tensorCodomainIncludeRight f g) K hK) := sorry

end ModuleCat.SquareZeroExtension

