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
public import stacks_project.Chap91.Lemma_91_15_1_Kernel
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
def liftCoeff (f : R' →+* R) [f.IsSquareZeroExtension] (r : R) : R' :=
  have := Classical.decEq R
  if r = 0 then 0
  else Function.surjInv (RingHom.IsSquareZeroExtension.surjective (f := f)) r

/-- `liftCoeff` preserves zero. -/
theorem liftCoeff_zero (f : R' →+* R) [f.IsSquareZeroExtension] :
    liftCoeff f 0 = 0 := sorry

/-- `liftCoeff` is a section of the square-zero surjection. -/
theorem liftCoeff_spec (f : R' →+* R) [f.IsSquareZeroExtension] (r : R) :
    f (liftCoeff f r) = r := sorry

/-- Restrict a coefficient in `R'` to the kernel of a square-zero surjection, sending
non-kernel coefficients to `0`. -/
def coeffToKer (f : R' →+* R) [f.IsSquareZeroExtension] (r : R') : RingHom.ker f :=
  have := Classical.decEq R
  if h : f r = 0 then ⟨r, h⟩ else 0

/-- `coeffToKer` preserves zero. -/
theorem coeffToKer_zero (f : R' →+* R) [f.IsSquareZeroExtension] :
    coeffToKer f 0 = 0 := sorry

/-- Lift an `R`-linear map of free modules along a square-zero surjection by lifting matrix
coefficients of the images of basis vectors. -/
def liftFreeLinearMap (f : R' →+* R) [f.IsSquareZeroExtension] {ι κ : Type u}
    (φ : ModuleCat.Free.obj.{u, u} R ι ⟶ ModuleCat.Free.obj.{u, u} R κ) :
    ModuleCat.Free.obj.{u, u} R' ι ⟶ ModuleCat.Free.obj.{u, u} R' κ :=
  ModuleCat.ofHom
    (Finsupp.lift (κ →₀ R') R' ι fun i ↦
      Finsupp.mapRange (liftCoeff f)
        (have := Classical.decEq R; dif_pos (rfl : (0 : R) = 0))
        (φ.hom (Finsupp.single i (1 : R))))

/-- `liftFreeLinearMap` on a basis vector lifts the finitely supported matrix column of `φ`. -/
theorem liftFreeLinearMap_single (f : R' →+* R) [f.IsSquareZeroExtension] {ι κ : Type u}
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
abbrev kernelSingleComplex (f : R' →+* R) [f.IsSquareZeroExtension] :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  (HomologicalComplex.single (ModuleCat.{u} R) (up ℤ) (0 : ℤ)).obj (kernelModule f)

/-- The shifted derived tensor `(K ⊗[R]^L I[0])⟦2⟧`. -/
abbrev tensorKernelShift (f : R' →+* R) [f.IsSquareZeroExtension]
    (K : DerivedCategory (ModuleCat.{u} R)) :
    DerivedCategory (ModuleCat.{u} R) :=
  (K ⊗[R]^L kernelSingle f)⟦(2 : ℤ)⟧

/-- The isomorphism `(K ⊗[R]^L I[0])⟦2⟧ ≅ (K⟦2⟧) ⊗[R]^L I[0]`. -/
noncomputable def tensorKernelShift_iso_tensorShift
    (f : R' →+* R) [f.IsSquareZeroExtension]
    (K : DerivedCategory (ModuleCat.{u} R)) :
    tensorKernelShift f K ≅
      (K⟦(2 : ℤ)⟧ ⊗[R]^L kernelSingle f) :=
  ((DerivedTensor.Right.functor (kernelSingle f)).commShiftIso (2 : ℤ)).symm.app K

/-- The map `(α ⊗ id_{I[0]})⟦2⟧` induced by a morphism of derived modules. -/
def tensorKernelShiftMap (f : R' →+* R) [f.IsSquareZeroExtension]
    {K L : DerivedCategory (ModuleCat.{u} R)} (α : K ⟶ L) :
    tensorKernelShift f K ⟶ tensorKernelShift f L :=
  (shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (2 : ℤ)).map
    ((DerivedTensor.Right.functor (kernelSingle f)).map α)

/-- `tensorKernelShiftMap` is the shift of derived tensor against `I[0]`. -/
theorem tensorKernelShiftMap_apply (f : R' →+* R) [f.IsSquareZeroExtension]
    {K L : DerivedCategory (ModuleCat.{u} R)} (α : K ⟶ L) :
    tensorKernelShiftMap f α =
      (shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (2 : ℤ)).map
        ((DerivedTensor.Right.functor (kernelSingle f)).map α) := sorry

/-- A chosen integer witnessing that a derived object is cohomologically bounded above. -/
def isBoundedAboveBound (K : DerivedCategory (ModuleCat.{u} R))
    (hK : K.IsBoundedAbove) : ℤ :=
  Classical.choose hK

instance instIsLE_isBoundedAboveBound (K : DerivedCategory (ModuleCat.{u} R))
    (hK : K.IsBoundedAbove) :
    K.IsLE (isBoundedAboveBound K hK) :=
  Classical.choose_spec hK

instance instObjPreimage_isLE (K : DerivedCategory (ModuleCat.{u} R)) {n : ℤ}
    [K.IsLE n] :
    (DerivedCategory.Q.objPreimage K).IsLE n :=
  (DerivedCategory.isLE_Q_obj_iff (DerivedCategory.Q.objPreimage K) n).mp
    (DerivedCategory.TStructure.t.isLE_of_iso
      (DerivedCategory.Q.objObjPreimageIso K).symm n)

/-- A bounded-above cochain representative of a derived object, obtained by truncating a
chosen preimage. -/
def boundedRepresentative (K : DerivedCategory (ModuleCat.{u} R))
    (hK : K.IsBoundedAbove) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  (DerivedCategory.Q.objPreimage K).truncLE (isBoundedAboveBound K hK)

/-- One degree of a bounded-above termwise-free replacement: free generators, the comparison
to the original complex, and the cochain differential as a map of free modules. -/
structure FreeReplacementStage (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) (k : ℕ) where
  /-- Generating type of the free module in degree `a + 1 - k`. -/
  gens : Type u
  /-- Generating type of the free module one degree higher. -/
  gensHigher : Type u
  /-- Comparison from the free module to the original complex. -/
  toK : ModuleCat.Free.obj.{u, u} R gens ⟶ K.X (a + 1 - k)
  /-- The cochain differential as an `R`-linear map of free modules on the chosen generators. -/
  dOut : ModuleCat.Free.obj.{u, u} R gens ⟶ ModuleCat.Free.obj.{u, u} R gensHigher

/-- Degree identity used to compare `K.X a` with the `k = 1` stage target. -/
theorem freeReplacement_stage1_deg (a : ℤ) : a = a + 1 - (1 : ℕ) := sorry

/-- Degree identity aligning the pullback target with the previous stage comparison. -/
theorem freeReplacement_pullbackDeg (a : ℤ) (k : ℕ) :
    a + 1 - ((k + 1 : ℕ) : ℤ) = a - (k + 1 : ℕ) + 1 := sorry

/-- Degree identity aligning the new stage comparison with the pullback source. -/
theorem freeReplacement_toKDeg (a : ℤ) (k : ℕ) :
    a - (k + 1 : ℕ) = a + 1 - ((k + 2 : ℕ) : ℤ) := sorry

/-- Termwise-free replacement data in offset `k` below the bound, constructed by descending
induction so that each differential lands in the kernel of the next. -/
def freeReplacementStage (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    (k : ℕ) → FreeReplacementStage K a k
  | 0 =>
    { gens := PEmpty.{u + 1}
      gensHigher := PEmpty.{u + 1}
      toK := 0
      dOut := 0 }
  | 1 =>
    { gens := (K.X a : Type u)
      gensHigher := PEmpty.{u + 1}
      toK := ModuleCat.Free.desc.{u, u} R (TypeCat.ofHom fun x : (K.X a : Type u) ↦ x) ≫
        eqToHom (congrArg K.X (freeReplacement_stage1_deg a))
      dOut := 0 }
  | k + 2 =>
    let prev := freeReplacementStage K a (k + 1)
    let i : ℤ := a - (k + 1 : ℕ)
    let kerToK := kernel.ι prev.dOut ≫ prev.toK ≫
      eqToHom (congrArg K.X (freeReplacement_pullbackDeg a k))
    let W := pullback (K.d i (i + 1)) kerToK
    { gens := (W : Type u)
      gensHigher := prev.gens
      toK := ModuleCat.Free.desc.{u, u} R (TypeCat.ofHom fun x : (W : Type u) ↦ x) ≫
        pullback.fst (K.d i (i + 1)) kerToK ≫
        eqToHom (congrArg K.X (freeReplacement_toKDeg a k))
      dOut := ModuleCat.Free.desc.{u, u} R (TypeCat.ofHom fun x : (W : Type u) ↦ x) ≫
        pullback.snd (K.d i (i + 1)) kerToK ≫ kernel.ι prev.dOut }

/-- The `ℕ`-offset of cohomological degree `n` relative to the bound `a`. -/
def freeReplacementOffset (a n : ℤ) : ℕ :=
  Int.toNat (a + 1 - n)

/-- Generating type of the termwise-free replacement in degree `n`. -/
def freeReplacementGens (K : CochainComplex (ModuleCat.{u} R) ℤ) (a n : ℤ) : Type u :=
  (freeReplacementStage K a (freeReplacementOffset a n)).gens

/-- The generating type one degree higher in the free replacement agrees with the generating
type of the next cohomological degree. -/
theorem freeReplacement_gensHigher_eq (K : CochainComplex (ModuleCat.{u} R) ℤ) (a i j : ℤ)
    (hij : i + 1 = j) :
    (freeReplacementStage K a (freeReplacementOffset a i)).gensHigher =
      freeReplacementGens K a j := sorry

/-- The bounded-above termwise-free cochain complex replacing `K`. -/
def freeReplacement (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ where
  X n := ModuleCat.Free.obj.{u, u} R (freeReplacementGens K a n)
  d i j :=
    if hij : i + 1 = j then
      (freeReplacementStage K a (freeReplacementOffset a i)).dOut ≫
        eqToHom (congrArg (fun ι : Type u ↦ ModuleCat.Free.obj.{u, u} R ι)
          (freeReplacement_gensHigher_eq K a i j hij))
    else 0
  shape i j hij := sorry
  d_comp_d' i j k hij hjk := sorry

/-- The offset description of degree `n` recovers `n` after subtracting from `a + 1`,
provided `n ≤ a + 1`. -/
theorem freeReplacement_degree_eq (a n : ℤ) (hn : n ≤ a + 1) :
    a + 1 - freeReplacementOffset a n = n := sorry

/-- Comparison from the termwise-free replacement to the original bounded-above complex.
In degrees `n > a + 1` both sides vanish, so the component is the zero map. -/
def freeReplacementComparison (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    freeReplacement K a ⟶ K where
  f n :=
    if hn : n ≤ a + 1 then
      (freeReplacementStage K a (freeReplacementOffset a n)).toK ≫
        eqToHom (congrArg K.X (freeReplacement_degree_eq a n hn))
    else
      0
  comm' i j hij := sorry

/-- `Q.map` of the free-replacement comparison is an isomorphism. -/
instance instIsIso_Q_freeReplacementComparison
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    IsIso (DerivedCategory.Q.map (freeReplacementComparison K a)) := sorry

/-- Inverse of `Q.map` of the free-replacement comparison. -/
def freeReplacementComparisonDerivedInv
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj (freeReplacement K a) :=
  (asIso (DerivedCategory.Q.map (freeReplacementComparison K a))).inv

/-- Convert a finitely supported `ker f`-valued function into an elementary tensor. -/
def finsuppKerToTensor (f : R' →+* R) [f.IsSquareZeroExtension] {ι : Type u}
    (x : ι →₀ RingHom.ker f) :
    TensorProduct R (ι →₀ R) (RingHom.ker f) :=
  x.sum fun a v ↦ TensorProduct.tmul R (Finsupp.single a (1 : R)) v

/-- The obstruction coefficients of `d' ∘ d'` on a generator of the free replacement. -/
def omegaOnGens (f : R' →+* R) [f.IsSquareZeroExtension]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a i : ℤ)
    (x : freeReplacementGens K a i) :
    freeReplacementGens K a (i + 2) →₀ RingHom.ker f :=
  let h₁ := freeReplacement_gensHigher_eq K a i (i + 1) rfl
  let h₂ := freeReplacement_gensHigher_eq K a (i + 1) (i + 2)
      ((add_assoc i (1 : ℤ) 1).trans
        (congrArg (HAdd.hAdd i) (one_add_one_eq_two : (1 : ℤ) + 1 = 2)))
  let y :=
    (liftFreeLinearMap f
        (freeReplacementStage K a (freeReplacementOffset a i)).dOut).hom
      (Finsupp.single x (1 : R'))
  let y' := Finsupp.equivMapDomain (Equiv.cast h₁) y
  let z :=
    (liftFreeLinearMap f
        (freeReplacementStage K a (freeReplacementOffset a (i + 1))).dOut).hom y'
  Finsupp.mapRange (coeffToKer f)
    (have := Classical.decEq R; dif_pos (RingHom.map_zero f))
    (Finsupp.equivMapDomain (Equiv.cast h₂) z)

/-- The cochain-level component of `ω` on the free replacement, with values in the termwise
tensor `P^{i+2} ⊗ I`. -/
def canonicalClassComponent (f : R' →+* R) [f.IsSquareZeroExtension]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a i : ℤ) :
    (freeReplacement K a).X i ⟶
      (freeReplacement K a).X (i + 2) ⊗ kernelModule f :=
  ModuleCat.ofHom
    { toFun := fun x ↦
        finsuppKerToTensor f
          (Finsupp.lift (freeReplacementGens K a (i + 2) →₀ RingHom.ker f) R
              (freeReplacementGens K a i)
              (fun g ↦ omegaOnGens f K a i g) x)
      map_add' := sorry
      map_smul' := sorry }

/-- Termwise tensor of a cochain complex with the square-zero kernel. -/
abbrev tensorKernelComplex (f : R' →+* R) [f.IsSquareZeroExtension]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  K ⊗ kernelSingleComplex f

/-- The cochain map `P^• ⟶ (P^• ⊗ I[0])⟦2⟧` presenting `ω` on a termwise-free replacement. -/
def canonicalClass_ofFree (f : R' →+* R) [f.IsSquareZeroExtension]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    freeReplacement K a ⟶ (tensorKernelComplex f (freeReplacement K a))⟦(2 : ℤ)⟧ where
  f i :=
    canonicalClassComponent f K a i ≫
      ιTensorObj (freeReplacement K a) (kernelSingleComplex f)
        (i + 2) 0 (i + 2) (add_zero (i + 2))
  comm' _ _ _ := sorry

/-- The derived-tensor counit against `I[0]` is invertible on cochain complexes. -/
theorem isIso_counitAppOfQ_kernelSingle (f : R' →+* R) [f.IsSquareZeroExtension]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    IsIso (DerivedTensor.Bifunctor.counitAppOfQ K (kernelSingleComplex f)) := sorry

instance instIsIso_counitAppOfQ_kernelSingle (f : R' →+* R) [f.IsSquareZeroExtension]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    IsIso (DerivedTensor.Bifunctor.counitAppOfQ K (kernelSingleComplex f)) :=
  isIso_counitAppOfQ_kernelSingle f K

/-- Comparison from the total tensor with `I[0]` to the fixed-right derived tensor against
`I[0]`. -/
def termwiseToDerivedTensor (f : R' →+* R) [f.IsSquareZeroExtension]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    DerivedCategory.Q.obj (tensorKernelComplex f K) ⟶
      DerivedCategory.Q.obj K ⊗[R]^L kernelSingle f :=
  inv (DerivedTensor.Bifunctor.counitAppOfQ K (kernelSingleComplex f)) ≫
    (DerivedTensor.Bifunctor.Right.isoApp (kernelSingle f) (DerivedCategory.Q.obj K)).inv

/-- `Q.map` of the truncation map of a bounded-above representative is an isomorphism. -/
instance instIsIso_Q_ιTruncLE
    (K : DerivedCategory (ModuleCat.{u} R)) (hK : K.IsBoundedAbove) :
    IsIso
      (DerivedCategory.Q.map
        ((DerivedCategory.Q.objPreimage K).ιTruncLE (isBoundedAboveBound K hK))) := sorry

/-- Inverse of `Q.map` of the truncation comparison of a bounded-above representative. -/
def ιTruncLEDerivedInv (K : DerivedCategory (ModuleCat.{u} R)) (hK : K.IsBoundedAbove) :
    DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage K) ⟶
      DerivedCategory.Q.obj (boundedRepresentative K hK) :=
  (asIso (DerivedCategory.Q.map
      ((DerivedCategory.Q.objPreimage K).ιTruncLE (isBoundedAboveBound K hK)))).inv

/-- The canonical morphism `ω(K) : K ⟶ K ⊗[R]^L I[2]` in `D(R)`. -/
def canonicalClass (f : R' →+* R) [f.IsSquareZeroExtension]
    (K : DerivedCategory (ModuleCat.{u} R)) (hK : K.IsBoundedAbove) :
    K ⟶ tensorKernelShift f K :=
  let a := isBoundedAboveBound K hK
  let P := freeReplacement (boundedRepresentative K hK) a
  (DerivedCategory.Q.objObjPreimageIso K).inv ≫
    ιTruncLEDerivedInv K hK ≫
    freeReplacementComparisonDerivedInv (boundedRepresentative K hK) a ≫
    DerivedCategory.Q.map (canonicalClass_ofFree f (boundedRepresentative K hK) a) ≫
      (DerivedCategory.Q.commShiftIso (2 : ℤ)).hom.app
        (tensorKernelComplex f P) ≫
      ((shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (2 : ℤ)).map
        (termwiseToDerivedTensor f P)) ≫
      ((shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (2 : ℤ)).map
        ((DerivedTensor.Right.functor (kernelSingle f)).map
          (DerivedCategory.Q.map
              (freeReplacementComparison (boundedRepresentative K hK) a) ≫
            DerivedCategory.Q.map
              ((DerivedCategory.Q.objPreimage K).ιTruncLE a) ≫
            (DerivedCategory.Q.objObjPreimageIso K).hom)))

/-- `canonicalClass` is `Q.map` of the cochain-level factorization of lifted `d' ∘ d'` on a
termwise-free replacement of a bounded-above representative, transported to `K`. -/
theorem canonicalClass_spec (f : R' →+* R) [f.IsSquareZeroExtension]
    (K : DerivedCategory (ModuleCat.{u} R)) (hK : K.IsBoundedAbove) :
    canonicalClass f K hK =
      (let a := isBoundedAboveBound K hK
        let P := freeReplacement (boundedRepresentative K hK) a
        (DerivedCategory.Q.objObjPreimageIso K).inv ≫
          ιTruncLEDerivedInv K hK ≫
          freeReplacementComparisonDerivedInv (boundedRepresentative K hK) a ≫
          DerivedCategory.Q.map (canonicalClass_ofFree f (boundedRepresentative K hK) a) ≫
            (DerivedCategory.Q.commShiftIso (2 : ℤ)).hom.app
              (tensorKernelComplex f P) ≫
            ((shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (2 : ℤ)).map
              (termwiseToDerivedTensor f P)) ≫
            ((shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (2 : ℤ)).map
              ((DerivedTensor.Right.functor (kernelSingle f)).map
                (DerivedCategory.Q.map
                    (freeReplacementComparison (boundedRepresentative K hK) a) ≫
                  DerivedCategory.Q.map
                    ((DerivedCategory.Q.objPreimage K).ιTruncLE a) ≫
                  (DerivedCategory.Q.objObjPreimageIso K).hom)))) := sorry

/-- Derived extension of scalars of a bounded-above object remains bounded above. -/
theorem derivedExtensionOfScalars_isBoundedAbove
    {A : Type u} [CommRing A] (σ : R →+* A)
    (K : DerivedCategory (ModuleCat.{u} R)) (hK : K.IsBoundedAbove) :
    ((ModuleCat.derivedExtensionOfScalars σ).obj K).IsBoundedAbove := sorry

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

/-- `kernelBaseChangeModule` is the adjunct of `kernelToBaseChange` along
`R → S' ⊗[R'] R`. -/
theorem kernelBaseChangeModule_spec (f : R' →+* R) [f.IsSquareZeroExtension]
    {S' : Type u} [CommRing S'] (g : R' →+* S') :
    kernelBaseChangeModule f g =
      ((ModuleCat.extendRestrictScalarsAdj (tensorCodomainIncludeRight f g)).homEquiv
          (kernelModule f) (kernelModule (tensorCodomainRingHom f g))).symm
        (ModuleCat.ofHom (X := kernelModule f)
          (Y := (ModuleCat.restrictScalars (tensorCodomainIncludeRight f g)).obj
            (kernelModule (tensorCodomainRingHom f g)))
          { toFun := fun i ↦ kernelToBaseChange f g i
            map_add' := (kernelToBaseChange f g).map_add
            map_smul' := sorry }) := sorry

/-- The derived comparison `I[0] ⊗[R]^L S ⟶ J[0]` induced by `kernelBaseChange`. -/
def kernelBaseChangeDerivedRight (f : R' →+* R) [f.IsSquareZeroExtension]
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

/-- `kernelBaseChangeDerivedRight` is `Q` of the cochain-level extension of scalars of
`I[0]`, followed by `singleFunctor` of `kernelBaseChangeModule`. -/
theorem kernelBaseChangeDerivedRight_spec (f : R' →+* R) [f.IsSquareZeroExtension]
    {S' : Type u} [CommRing S'] (g : R' →+* S') :
    kernelBaseChangeDerivedRight f g =
      (Functor.LeftDerived.Homotopy.cochainCounit
          (ModuleCat.extendScalars (tensorCodomainIncludeRight f g))).app
          (kernelSingleComplex f) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex
              (ModuleCat.extendScalars (tensorCodomainIncludeRight f g))
              (up ℤ) (0 : ℤ)).hom.app (kernelModule f)) ≫
        (DerivedCategory.singleFunctor (ModuleCat.{u} (tensorCodomain f g)) (0 : ℤ)).map
          (kernelBaseChangeModule f g) := sorry

/-- The map `I[0]` to `J[0]` in `D(S)` induced by `kernelBaseChange`. -/
def kernelBaseChangeSingle (f : R' →+* R) [f.IsSquareZeroExtension]
    {S' : Type u} [CommRing S'] (g : R' →+* S') :
    (singleFunctor (ModuleCat.{u} (tensorCodomain f g)) (0 : ℤ)).obj
        ((ModuleCat.extendScalars (tensorCodomainIncludeRight f g)).obj
          (kernelModule f)) ⟶
      kernelSingle (tensorCodomainRingHom f g) :=
  (singleFunctor (ModuleCat.{u} (tensorCodomain f g)) (0 : ℤ)).map
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

end ModuleCat.SquareZeroExtension

