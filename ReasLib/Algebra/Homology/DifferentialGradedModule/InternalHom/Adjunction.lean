/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import ReasLib.Algebra.Homology.DifferentialGradedModule.InternalHom.Shift
public import ReasLib.Algebra.Homology.DifferentialGradedModule.TensorProduct

/-!
# Relative tensor and internal-Hom adjunctions

This file packages internal Hom from an arbitrary bundled left or right differential graded
module.  It exposes concrete currying and uncurrying before forming the two adjunctions with the
relative tensor complex.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory
open CochainComplex.HomComplex

namespace DifferentialGradedModule.InternalHom

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}

/-- Postcompose a homogeneous cochain by a morphism of target complexes. -/
def postcomp (M : CochainComplex (ModuleCat.{v} R) ℤ)
    {N N' : CochainComplex (ModuleCat.{v} R) ℤ} (g : N ⟶ N') (k : ℤ) :
    Cochain M N k →ₗ[R] Cochain M N' k where
  toFun := fun f ↦ f.comp (Cochain.ofHom g) (add_zero k)
  map_add' := sorry
  map_smul' := sorry

namespace OfLeft

/-- The graded pieces of a bundled left DG module agree with those of its underlying complex. -/
theorem source_X_eq (M : LeftDifferentialGradedModule.{u, v} A) :
    M.X = fun n ↦ M.toCochainComplex.X n := sorry

/-- Transporting the differential of a bundled left DG module along `source_X_eq` gives its
underlying-complex differential. -/
theorem source_d_eq (M : LeftDifferentialGradedModule.{u, v} A) :
    Eq.rec (motive := fun X _ ↦ (n : ℤ) → X n →ₗ[R] X (n + 1))
      M.d (source_X_eq M) = underlyingDifferential M.toCochainComplex := sorry

/-- A bundled left DG module in the fixed-underlying fiber used by internal Hom. -/
def source (M : LeftDifferentialGradedModule.{u, v} A) :
    LeftDifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.toCochainComplex.X n) (underlyingDifferential M.toCochainComplex) where
  toLeftDifferentialGradedModule := M
  X_eq := source_X_eq M
  d_eq := source_d_eq M

/-- The right DG `A`-module `Hom•(M, N)` induced by a left DG `A`-module `M`. -/
def obj (M : LeftDifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) : DifferentialGradedModule.{u, v} A :=
  (rightWithFixedUnderlying N (source M)).toRightDifferentialGradedModule

/-- Regard an element of `Hom•(M, N)` as a cochain of the same degree. -/
abbrev asCochain (M : LeftDifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) {k : ℤ} (f : (obj M N).X k) :
    Cochain M.toCochainComplex N k :=
  f

/-- Postcomposition gives the action of internal Hom on a target-complex morphism. -/
def map (M : LeftDifferentialGradedModule.{u, v} A)
    {N N' : CochainComplex (ModuleCat.{v} R) ℤ} (g : N ⟶ N') :
    obj M N ⟶ obj M N' where
  hom k := postcomp M.toCochainComplex g k
  comm_d := sorry
  comm_smul := sorry

/-- Fixed-source internal Hom from a left DG module, functorial in the target complex. -/
def functor (M : LeftDifferentialGradedModule.{u, v} A) :
    CochainComplex (ModuleCat.{v} R) ℤ ⥤ DifferentialGradedModule.{u, v} A where
  obj := obj M
  map := map M
  map_id := sorry
  map_comp := sorry

/-- Reorder the degrees used when currying a tensor-complex morphism. -/
theorem curryDegree (p q r : ℤ) (h : q + p = r) : p + q = r := sorry

/-- The degree-`p` cochain obtained by fixing an element of the right tensor factor. -/
def curryCochain (M' : DifferentialGradedModule.{u, v} A)
    (M : LeftDifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) (f : TensorProduct.complex M' M ⟶ N)
    (p : ℤ) (m : M'.X p) : Cochain M.toCochainComplex N p :=
  Cochain.mk fun q r h ↦ ModuleCat.ofHom <|
    ModuleCat.castLinearMap (congrArg N.X (curryDegree p q r h))
      ((f.f (p + q)).hom.comp (TensorProduct.tmulRight M' M m))

/-- Currying in one homogeneous degree is linear in the fixed tensor input. -/
def curryComponent (M' : DifferentialGradedModule.{u, v} A)
    (M : LeftDifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) (f : TensorProduct.complex M' M ⟶ N)
    (p : ℤ) : M'.X p →ₗ[R] (obj M N).X p where
  toFun := curryCochain M' M N f p
  map_add' := sorry
  map_smul' := sorry

/-- Curry a map from a relative tensor complex into a right-DG-module morphism. -/
def curry (M' : DifferentialGradedModule.{u, v} A)
    (M : LeftDifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) (f : TensorProduct.complex M' M ⟶ N) :
    M' ⟶ obj M N where
  hom := curryComponent M' M N f
  comm_d := sorry
  comm_smul := sorry

/- The left-source counterpart of `OfRight.curry_apply` exposes the same
  pure-tensor computation without unfolding the cochain construction. -/
/-- Evaluation of left-source currying on homogeneous elements. -/
@[simp, stacks 0FQ4 "left-source currying on pure tensors"]
theorem curry_apply (M' : DifferentialGradedModule.{u, v} A)
    (M : LeftDifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ)
    (f : TensorProduct.complex M' M ⟶ N)
    (p q : ℤ) (m : M'.X p) (x : M.X q) :
    (asCochain M N ((curry M' M N f).hom p m)).v q (p + q)
        (add_comm q p) x =
      (f.f (p + q)) (TensorProduct.tmul M' M m x) := sorry

/-- Reorder a bidegree decomposition for evaluation during uncurrying. -/
theorem uncurryDegree (p q n : ℤ) (h : p + q = n) : q + p = n := sorry

/-- Uncurrying on one homogeneous tensor summand. -/
def uncurryComponent (M' : DifferentialGradedModule.{u, v} A)
    (M : LeftDifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) (g : M' ⟶ obj M N)
    (n p q : ℤ) (h : p + q = n) :
    TensorProduct.baseTensor (R := R) (M'.X p) (M.X q) ⟶ N.X n :=
  ModuleCat.TensorProduct.liftOfBilinear R
    (fun m x ↦ (asCochain M N (g.hom p m)).v q n (uncurryDegree p q n h) x)
    sorry sorry sorry sorry

/-- The homogeneous pairing underlying left-source uncurrying. -/
def uncurryPairing (M' : DifferentialGradedModule.{u, v} A)
    (M : LeftDifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) (g : M' ⟶ obj M N) :
    TensorProduct.Pairing M' M N :=
  fun p q ↦ uncurryComponent M' M N g (p + q) p q rfl

/-- The raw uncurrying map before imposing the `A`-balancing quotient. -/
def uncurryRaw (M' : DifferentialGradedModule.{u, v} A)
    (M : LeftDifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) (g : M' ⟶ obj M N) (n : ℤ) :
    TensorProduct.rawTerm M' M n →ₗ[R] N.X n :=
  TensorProduct.rawDesc M' M (uncurryPairing M' M N g) n

/-- The left-source uncurrying pairing is balanced over `A`. -/
theorem uncurry_balanced (M' : DifferentialGradedModule.{u, v} A)
    (M : LeftDifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) (g : M' ⟶ obj M N) :
    TensorProduct.IsBalanced M' M (uncurryPairing M' M N g) := sorry

/-- The uncurrying map descended to one degree of the relative tensor quotient. -/
def uncurryLinear (M' : DifferentialGradedModule.{u, v} A)
    (M : LeftDifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) (g : M' ⟶ obj M N) (n : ℤ) :
    TensorProduct.family M' M n →ₗ[R] N.X n :=
  TensorProduct.descLinear M' M (uncurryPairing M' M N g)
    (uncurry_balanced M' M N g) n

/-- The descended left-source uncurrying pairing commutes with the differentials. -/
theorem uncurry_comm (M' : DifferentialGradedModule.{u, v} A)
    (M : LeftDifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) (g : M' ⟶ obj M N) :
    TensorProduct.IsDifferentialCompatible M' M (uncurryPairing M' M N g) := sorry

/-- Uncurry a right-DG-module morphism into a map from the relative tensor complex. -/
def uncurry (M' : DifferentialGradedModule.{u, v} A)
    (M : LeftDifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) (g : M' ⟶ obj M N) :
    TensorProduct.complex M' M ⟶ N :=
  TensorProduct.lift M' M (uncurryPairing M' M N g)
    (uncurry_balanced M' M N g) (uncurry_comm M' M N g)

/-- Evaluation of left-source uncurrying on a pure tensor. -/
theorem uncurry_tmul (M' : DifferentialGradedModule.{u, v} A)
    (M : LeftDifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) (g : M' ⟶ obj M N)
    (p q : ℤ) (m : M'.X p) (x : M.X q) :
    (uncurry M' M N g).f (p + q) (TensorProduct.tmul M' M m x) =
      (asCochain M N (g.hom p m)).v q (p + q) (add_comm q p) x := sorry

/-- Lemma 22.13.2 (0FQ4): maps into `Hom•(M, N)` are naturally equivalent to maps
`M' ⊗_A M ⟶ N`. -/
@[stacks 0FQ4 "relative tensor and internal Hom adjunction for a left DG source"]
def homEquiv (M' : DifferentialGradedModule.{u, v} A)
    (M : LeftDifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) :
    (M' ⟶ obj M N) ≃ (TensorProduct.complex M' M ⟶ N) where
  toFun := uncurry M' M N
  invFun := curry M' M N
  left_inv := sorry
  right_inv := sorry

/-- Relative tensoring with a fixed left DG module is left adjoint to its internal Hom. -/
def adjunction (M : LeftDifferentialGradedModule.{u, v} A) :
    TensorProduct.rightModuleFunctor M ⊣ functor M :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M' N ↦ (homEquiv M' M N).symm
      homEquiv_naturality_left_symm := sorry
      homEquiv_naturality_right := sorry }

end OfLeft

namespace OfRight

/-- The graded pieces of a bundled right DG module agree with those of its underlying complex. -/
theorem source_X_eq (M : DifferentialGradedModule.{u, v} A) :
    M.X = fun n ↦ M.toCochainComplex.X n := sorry

/-- Transporting the differential of a bundled right DG module along `source_X_eq` gives its
underlying-complex differential. -/
theorem source_d_eq (M : DifferentialGradedModule.{u, v} A) :
    Eq.rec (motive := fun X _ ↦ (n : ℤ) → X n →ₗ[R] X (n + 1))
      M.d (source_X_eq M) = underlyingDifferential M.toCochainComplex := sorry

/-- A bundled right DG module in the fixed-underlying fiber used by internal Hom. -/
def source (M : DifferentialGradedModule.{u, v} A) :
    DifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.toCochainComplex.X n) (underlyingDifferential M.toCochainComplex) where
  toRightDifferentialGradedModule := M
  X_eq := source_X_eq M
  d_eq := source_d_eq M

/-- The left DG `A`-module `Hom•(M, N)` induced by a right DG `A`-module `M`. -/
def obj (M : DifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) : LeftDifferentialGradedModule.{u, v} A :=
  (leftWithFixedUnderlying N (source M)).toLeftDifferentialGradedModule

/-- Regard an element of `Hom•(M, N)` as a cochain of the same degree. -/
abbrev asCochain (M : DifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) {k : ℤ} (f : (obj M N).X k) :
    Cochain M.toCochainComplex N k :=
  f

/-- Postcomposition gives the action of right-source internal Hom on a target morphism. -/
def map (M : DifferentialGradedModule.{u, v} A)
    {N N' : CochainComplex (ModuleCat.{v} R) ℤ} (g : N ⟶ N') :
    obj M N ⟶ obj M N' where
  hom k := postcomp M.toCochainComplex g k
  comm_d := sorry
  comm_smul := sorry

/-- Fixed-source internal Hom from a right DG module, functorial in the target complex. -/
def functor (M : DifferentialGradedModule.{u, v} A) :
    CochainComplex (ModuleCat.{v} R) ℤ ⥤ LeftDifferentialGradedModule.{u, v} A where
  obj := obj M
  map := map M
  map_id := sorry
  map_comp := sorry

/-- The degree-`q` cochain obtained by fixing an element of the left tensor factor, including
the Koszul sign which exchanges the two homogeneous inputs. -/
def curryCochain (M : DifferentialGradedModule.{u, v} A)
    (M' : LeftDifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) (f : TensorProduct.complex M M' ⟶ N)
    (q : ℤ) (x : M'.X q) : Cochain M.toCochainComplex N q :=
  Cochain.mk fun p r h ↦ ModuleCat.ofHom <|
    ((p * q).negOnePow : R) • ModuleCat.castLinearMap (congrArg N.X h)
      ((f.f (p + q)).hom.comp (TensorProduct.tmulLeft M M' x))

/-- Right-source currying in one degree is linear in the fixed left-module input. -/
def curryComponent (M : DifferentialGradedModule.{u, v} A)
    (M' : LeftDifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) (f : TensorProduct.complex M M' ⟶ N)
    (q : ℤ) : M'.X q →ₗ[R] (obj M N).X q where
  toFun := curryCochain M M' N f q
  map_add' := sorry
  map_smul' := sorry

/-- Curry a map from `M ⊗_A M'` into a left-DG-module morphism, using the Koszul-signed
tensor-order comparison. -/
def curry (M : DifferentialGradedModule.{u, v} A)
    (M' : LeftDifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) (f : TensorProduct.complex M M' ⟶ N) :
    M' ⟶ obj M N where
  hom := curryComponent M M' N f
  comm_d := sorry
  comm_smul := sorry

/-- Evaluation of right-source currying on homogeneous elements. -/
@[simp, stacks 0FQ6 "right-source currying on pure tensors"]
theorem curry_apply (M : DifferentialGradedModule.{u, v} A)
    (M' : LeftDifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) (f : TensorProduct.complex M M' ⟶ N)
    (p q : ℤ) (m : M.X p) (x : M'.X q) :
    (asCochain M N ((curry M M' N f).hom q x)).v p (p + q) rfl m =
      ((p * q).negOnePow : R) •
        (f.f (p + q)) (TensorProduct.tmul M M' m x) := sorry

/-- Koszul-signed uncurrying on one homogeneous summand of `M ⊗_A M'`. -/
def uncurryComponent (M : DifferentialGradedModule.{u, v} A)
    (M' : LeftDifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) (g : M' ⟶ obj M N)
    (n p q : ℤ) (h : p + q = n) :
    TensorProduct.baseTensor (R := R) (M.X p) (M'.X q) ⟶ N.X n :=
  ModuleCat.TensorProduct.liftOfBilinear R
    (fun m x ↦ ((p * q).negOnePow : R) •
      (asCochain M N (g.hom q x)).v p n h m)
    sorry sorry sorry sorry

/-- The homogeneous pairing underlying right-source uncurrying. -/
def uncurryPairing (M : DifferentialGradedModule.{u, v} A)
    (M' : LeftDifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) (g : M' ⟶ obj M N) :
    TensorProduct.Pairing M M' N :=
  fun p q ↦ uncurryComponent M M' N g (p + q) p q rfl

/-- The raw right-source uncurrying map before imposing balancing. -/
def uncurryRaw (M : DifferentialGradedModule.{u, v} A)
    (M' : LeftDifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) (g : M' ⟶ obj M N) (n : ℤ) :
    TensorProduct.rawTerm M M' n →ₗ[R] N.X n :=
  TensorProduct.rawDesc M M' (uncurryPairing M M' N g) n

/-- The right-source uncurrying pairing is balanced over `A`. -/
theorem uncurry_balanced (M : DifferentialGradedModule.{u, v} A)
    (M' : LeftDifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) (g : M' ⟶ obj M N) :
    TensorProduct.IsBalanced M M' (uncurryPairing M M' N g) := sorry

/-- The right-source uncurrying map descended to the relative tensor quotient. -/
def uncurryLinear (M : DifferentialGradedModule.{u, v} A)
    (M' : LeftDifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) (g : M' ⟶ obj M N) (n : ℤ) :
    TensorProduct.family M M' n →ₗ[R] N.X n :=
  TensorProduct.descLinear M M' (uncurryPairing M M' N g)
    (uncurry_balanced M M' N g) n

/-- The descended right-source uncurrying pairing commutes with the differentials. -/
theorem uncurry_comm (M : DifferentialGradedModule.{u, v} A)
    (M' : LeftDifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) (g : M' ⟶ obj M N) :
    TensorProduct.IsDifferentialCompatible M M' (uncurryPairing M M' N g) := sorry

/-- Uncurry a left-DG-module morphism into a map from `M ⊗_A M'`. -/
def uncurry (M : DifferentialGradedModule.{u, v} A)
    (M' : LeftDifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) (g : M' ⟶ obj M N) :
    TensorProduct.complex M M' ⟶ N :=
  TensorProduct.lift M M' (uncurryPairing M M' N g)
    (uncurry_balanced M M' N g) (uncurry_comm M M' N g)

/-- Evaluation of right-source uncurrying on a pure tensor. -/
theorem uncurry_tmul (M : DifferentialGradedModule.{u, v} A)
    (M' : LeftDifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) (g : M' ⟶ obj M N)
    (p q : ℤ) (m : M.X p) (x : M'.X q) :
    (uncurry M M' N g).f (p + q) (TensorProduct.tmul M M' m x) =
      ((p * q).negOnePow : R) •
        (asCochain M N (g.hom q x)).v p (p + q) rfl m := sorry

/-- Lemma 22.13.4 (0FQ6): after the Koszul tensor-order comparison, maps into
`Hom•(M, N)` are naturally equivalent to maps `M ⊗_A M' ⟶ N`. -/
@[stacks 0FQ6 "relative tensor and internal Hom adjunction for a right DG source"]
def homEquiv (M : DifferentialGradedModule.{u, v} A)
    (M' : LeftDifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) :
    (M' ⟶ obj M N) ≃ (TensorProduct.complex M M' ⟶ N) where
  toFun := uncurry M M' N
  invFun := curry M M' N
  left_inv := sorry
  right_inv := sorry

/-- Relative tensoring with a fixed right DG module is left adjoint to its left internal Hom. -/
def adjunction (M : DifferentialGradedModule.{u, v} A) :
    TensorProduct.leftModuleFunctor M ⊣ functor M :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M' N ↦ (homEquiv M M' N).symm
      homEquiv_naturality_left_symm := sorry
      homEquiv_naturality_right := sorry }

end OfRight

end DifferentialGradedModule.InternalHom
