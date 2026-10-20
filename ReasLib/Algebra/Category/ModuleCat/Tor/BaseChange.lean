/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Tensor
public import ReasLib.Algebra.Category.ModuleCat.Tor.TensorAction
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat Base Change for `Tor` over Tensor-Product Algebras

@stack 08HW

This leaf owns the source-faithful flat base-change comparison

`Tor_n^R(A, B) ⊗[A ⊗[R] B] (A' ⊗[R'] B') ⟶ Tor_n^{R'}(A', B')`.

The source and target `Tor` objects use the canonical tensor-product algebra
actions from `ModuleCat.Tor.TensorAction`.  The comparison is concrete; only
its linearity and invertibility laws are deferred.
-/

@[expose] public section

open CategoryTheory Algebra.TensorProduct
open scoped TensorProduct Algebra.TensorProduct.Right

universe u

noncomputable section

namespace CategoryTheory.ModuleCat.Tor.Flat.BaseChange

variable {R R' A B A' B' : Type u}
variable [CommRing R] [CommRing R'] [CommRing A] [CommRing B]
variable [CommRing A'] [CommRing B']
variable [Algebra R R'] [Algebra R A] [Algebra R B]
variable [Algebra R' A'] [Algebra R' B']

/-- The tensor-product algebra acting on the source `Tor` object. -/
@[stacks 08HW "source tensor-product algebra for Tor base change"]
abbrev sourceRing := A ⊗[R] B

/-- The tensor-product algebra acting on the target `Tor` object. -/
@[stacks 08HW "target tensor-product algebra for Tor base change"]
abbrev targetRing := A' ⊗[R'] B'

/-- The canonical map `R → A' ⊗[R'] B'` through `R'`. -/
@[stacks 08HW "base-ring map for the target Tor algebra"]
noncomputable def targetBaseRingHom : R →+* targetRing (R' := R') (A' := A') (B' := B') :=
  (algebraMap R' (targetRing (R' := R') (A' := A') (B' := B'))).comp (algebraMap R R')

/-- The map `A → A' ⊗[R'] B'` induced by `A ⊗[R] R' → A'`. -/
@[stacks 08HW "left-factor map for Tor base change"]
noncomputable def leftRingHom (aMap : A ⊗[R] R' →ₐ[R'] A') :
    A →+* targetRing (R' := R') (A' := A') (B' := B') :=
  (includeLeft : A' →ₐ[R'] targetRing (R' := R') (A' := A') (B' := B')).toRingHom.comp <|
    aMap.toRingHom.comp (includeLeft : A →ₐ[R] A ⊗[R] R').toRingHom

/-- The map `B → A' ⊗[R'] B'` induced by `R' ⊗[R] B → B'`. -/
@[stacks 08HW "right-factor map for Tor base change"]
noncomputable def rightRingHom (bMap : R' ⊗[R] B →ₐ[R'] B') :
    B →+* targetRing (R' := R') (A' := A') (B' := B') :=
  (includeRight : B' →ₐ[R'] targetRing (R' := R') (A' := A') (B' := B')).toRingHom.comp <|
    bMap.toRingHom.comp (includeRight : B →ₐ[R] R' ⊗[R] B).toRingHom

/-- The left-factor map agrees with the canonical base-ring map on `R`. -/
theorem leftRingHom_commutes (aMap : A ⊗[R] R' →ₐ[R'] A') (r : R) :
    leftRingHom (R := R) (R' := R') (A := A) (A' := A') (B' := B') aMap
        ((algebraMap R A) r) =
      targetBaseRingHom (R := R) (R' := R') (A' := A') (B' := B') r := sorry

/-- The right-factor map agrees with the canonical base-ring map on `R`. -/
theorem rightRingHom_commutes (bMap : R' ⊗[R] B →ₐ[R'] B') (r : R) :
    rightRingHom (R := R) (R' := R') (B := B) (A' := A') (B' := B') bMap
        ((algebraMap R B) r) =
      targetBaseRingHom (R := R) (R' := R') (A' := A') (B' := B') r := sorry

/-- The two factor maps into `A' ⊗[R'] B'` commute. -/
theorem leftRingHom_commute_rightRingHom
    (aMap : A ⊗[R] R' →ₐ[R'] A') (bMap : R' ⊗[R] B →ₐ[R'] B') (a : A) (b : B) :
    Commute
      (leftRingHom (R := R) (R' := R') (A := A) (A' := A') (B' := B') aMap a)
      (rightRingHom (R := R) (R' := R') (B := B) (A' := A') (B' := B') bMap b) := sorry

/-- The source diagram induces the canonical tensor-product ring map
`A ⊗[R] B → A' ⊗[R'] B'`. -/
@[stacks 08HW "tensor-product ring map for Tor base change"]
noncomputable def productMap
    (aMap : A ⊗[R] R' →ₐ[R'] A') (bMap : R' ⊗[R] B →ₐ[R'] B') :
    sourceRing (R := R) (A := A) (B := B) →+*
      targetRing (R' := R') (A' := A') (B' := B') :=
  letI : Algebra R (targetRing (R' := R') (A' := A') (B' := B')) :=
    (targetBaseRingHom (R := R) (R' := R') (A' := A') (B' := B')).toAlgebra
  let left : A →ₐ[R] targetRing (R' := R') (A' := A') (B' := B') :=
    { toRingHom := leftRingHom (R := R) (R' := R') (A := A) (A' := A') (B' := B') aMap
      commutes' := leftRingHom_commutes
        (R := R) (R' := R') (A := A) (A' := A') (B' := B') aMap }
  let right : B →ₐ[R] targetRing (R' := R') (A' := A') (B' := B') :=
    { toRingHom := rightRingHom (R := R) (R' := R') (B := B) (A' := A') (B' := B') bMap
      commutes' := rightRingHom_commutes
        (R := R) (R' := R') (B := B) (A' := A') (B' := B') bMap }
  (Algebra.TensorProduct.lift left right
    (leftRingHom_commute_rightRingHom
      (R := R) (R' := R') (A := A) (B := B) (A' := A') (B' := B') aMap bMap)).toRingHom

/-- The tensor-product base-change map restricts to the prescribed map on the
left factor. -/
theorem productMap_includeLeft
    (aMap : A ⊗[R] R' →ₐ[R'] A') (bMap : R' ⊗[R] B →ₐ[R'] B') (a : A) :
    productMap (R := R) (R' := R') (A := A) (B := B) (A' := A') (B' := B') aMap bMap
        ((includeLeft : A →ₐ[R] sourceRing (R := R) (A := A) (B := B)) a) =
      leftRingHom (R := R) (R' := R') (A := A) (A' := A') (B' := B') aMap a := sorry

/-- The tensor-product base-change map restricts to the prescribed map on the
right factor. -/
theorem productMap_includeRight
    (aMap : A ⊗[R] R' →ₐ[R'] A') (bMap : R' ⊗[R] B →ₐ[R'] B') (b : B) :
    productMap (R := R) (R' := R') (A := A) (B := B) (A' := A') (B' := B') aMap bMap
        ((includeRight : B →ₐ[R] sourceRing (R := R) (A := A) (B := B)) b) =
      rightRingHom (R := R) (R' := R') (B := B) (A' := A') (B' := B') bMap b := sorry

/-- The first-variable map after flat extension from `R` to `R'`. -/
@[stacks 08HW "first-variable Tor map after flat base change"]
noncomputable def leftHom (aMap : A ⊗[R] R' →ₐ[R'] A') :
    (ModuleCat.extendScalars (algebraMap R R')).obj (ModuleCat.of R A) ⟶ ModuleCat.of R' A' :=
  (ModuleCat.ExtendScalars.tensorIso (R := R) (S := R') (ModuleCat.of R A)).hom ≫
    ModuleCat.ofHom
      (aMap.comp (Algebra.TensorProduct.commRight R R' A).toAlgHom).toLinearMap

/-- The second-variable map after flat extension from `R` to `R'`. -/
@[stacks 08HW "second-variable Tor map after flat base change"]
noncomputable def rightHom (bMap : R' ⊗[R] B →ₐ[R'] B') :
    (ModuleCat.extendScalars (algebraMap R R')).obj (ModuleCat.of R B) ⟶ ModuleCat.of R' B' :=
  (ModuleCat.ExtendScalars.tensorIso (R := R) (S := R') (ModuleCat.of R B)).hom ≫
    ModuleCat.ofHom bMap.toLinearMap

/-- After flat base change, functoriality of `Tor` in both arguments reaches
`Tor_n^{R'}(A', B')`. -/
@[stacks 08HW "two-variable tail of the Tor base-change comparison"]
noncomputable def tail
    (aMap : A ⊗[R] R' →ₐ[R'] A') (bMap : R' ⊗[R] B →ₐ[R'] B') (n : ℕ) :
    (((CategoryTheory.Tor (ModuleCat R') n).obj
      ((ModuleCat.extendScalars (algebraMap R R')).obj (ModuleCat.of R A))).obj
        ((ModuleCat.extendScalars (algebraMap R R')).obj (ModuleCat.of R B))) ⟶
      ModuleCat.Tor.TensorAction.underlying (R := R') (A := A') (B := B') n :=
  ((CategoryTheory.Tor (ModuleCat R') n).map
      (leftHom (R := R) (R' := R') (A := A) (A' := A') aMap)).app
        ((ModuleCat.extendScalars (algebraMap R R')).obj (ModuleCat.of R B)) ≫
    ((CategoryTheory.Tor (ModuleCat R') n).obj (ModuleCat.of R' A')).map
      (rightHom (R := R) (R' := R') (B := B) (B' := B') bMap)

/-- The underlying `R'`-linear comparison before imposing the
`A' ⊗[R'] B'`-module structure. -/
@[stacks 08HW "underlying linear Tor base-change comparison"]
noncomputable def initialComparison
    (hflat : (algebraMap R R').Flat)
    (aMap : A ⊗[R] R' →ₐ[R'] A') (bMap : R' ⊗[R] B →ₐ[R'] B') (n : ℕ) :
    (ModuleCat.extendScalars (algebraMap R R')).obj
        (ModuleCat.Tor.TensorAction.underlying (R := R) (A := A) (B := B) n) ⟶
      ModuleCat.Tor.TensorAction.underlying (R := R') (A := A') (B := B') n :=
  ModuleCat.Tor.Flat.baseChange (algebraMap R R') hflat
      (ModuleCat.of R A) (ModuleCat.of R B) n ≫
    tail (R := R) (R' := R') (A := A) (B := B) (A' := A') (B' := B') aMap bMap n

/-- The adjoint of the underlying `R'`-linear comparison, before checking
linearity over `A ⊗[R] B`. -/
@[stacks 08HW "raw adjoint of the Tor base-change comparison"]
noncomputable def rawAdjoint
    (hflat : (algebraMap R R').Flat)
    (aMap : A ⊗[R] R' →ₐ[R'] A') (bMap : R' ⊗[R] B →ₐ[R'] B') (n : ℕ) :
    ModuleCat.Tor.TensorAction.underlying (R := R) (A := A) (B := B) n ⟶
      (ModuleCat.restrictScalars (algebraMap R R')).obj
        (ModuleCat.Tor.TensorAction.underlying (R := R') (A := A') (B := B') n) :=
  (ModuleCat.extendRestrictScalarsAdj (algebraMap R R')).homEquiv _ _
    (initialComparison (R := R) (R' := R') (A := A) (B := B) (A' := A') (B' := B')
      hflat aMap bMap n)

/-- The carrier function of the raw adjoint comparison. -/
@[stacks 08HW "carrier of the raw Tor base-change adjoint"]
noncomputable def rawAdjointFunction
    (hflat : (algebraMap R R').Flat)
    (aMap : A ⊗[R] R' →ₐ[R'] A') (bMap : R' ⊗[R] B →ₐ[R'] B') (n : ℕ) :
    ModuleCat.Tor.TensorAction.underlying (R := R) (A := A) (B := B) n →
      ModuleCat.Tor.TensorAction.underlying (R := R') (A := A') (B := B') n :=
  (rawAdjoint (R := R) (R' := R') (A := A) (B := B) (A' := A') (B' := B')
    hflat aMap bMap n).hom

/-- The raw adjoint preserves addition after the source and target tensor
actions are installed. -/
theorem rawAdjoint_map_add
    (hflat : (algebraMap R R').Flat)
    (aMap : A ⊗[R] R' →ₐ[R'] A') (bMap : R' ⊗[R] B →ₐ[R'] B') (n : ℕ)
    (x y : ModuleCat.Tor.TensorAction.underlying (R := R) (A := A) (B := B) n) :
    rawAdjointFunction (R := R) (R' := R') (A := A) (B := B) (A' := A') (B' := B')
        hflat aMap bMap n (x + y) =
      rawAdjointFunction (R := R) (R' := R') (A := A) (B := B) (A' := A') (B' := B')
          hflat aMap bMap n x +
        rawAdjointFunction (R := R) (R' := R') (A := A) (B := B) (A' := A') (B' := B')
          hflat aMap bMap n y := sorry

/-- The raw adjoint is linear for the tensor-product algebra map. -/
theorem rawAdjoint_map_smul
    (hflat : (algebraMap R R').Flat)
    (aMap : A ⊗[R] R' →ₐ[R'] A') (bMap : R' ⊗[R] B →ₐ[R'] B') (n : ℕ)
    (s : sourceRing (R := R) (A := A) (B := B))
    (x : ModuleCat.Tor.TensorAction.underlying (R := R) (A := A) (B := B) n) :
    letI : Module (sourceRing (R := R) (A := A) (B := B))
        (ModuleCat.Tor.TensorAction.underlying (R := R) (A := A) (B := B) n) :=
      ModuleCat.Tor.TensorAction.module (R := R) (A := A) (B := B) n
    letI : Module (targetRing (R' := R') (A' := A') (B' := B'))
        (ModuleCat.Tor.TensorAction.underlying (R := R') (A := A') (B := B') n) :=
      ModuleCat.Tor.TensorAction.module (R := R') (A := A') (B := B') n
    rawAdjointFunction (R := R) (R' := R') (A := A) (B := B) (A' := A') (B' := B')
        hflat aMap bMap n (s • x) =
      productMap (R := R) (R' := R') (A := A) (B := B) (A' := A') (B' := B')
          aMap bMap s •
        rawAdjointFunction (R := R) (R' := R') (A := A) (B := B) (A' := A') (B' := B')
          hflat aMap bMap n x := sorry

/-- The adjoint comparison as a morphism of `A ⊗[R] B`-modules. -/
@[stacks 08HW "adjoint Tor base-change comparison"]
noncomputable def adjoint
    (hflat : (algebraMap R R').Flat)
    (aMap : A ⊗[R] R' →ₐ[R'] A') (bMap : R' ⊗[R] B →ₐ[R'] B') (n : ℕ) :
    ModuleCat.Tor.TensorAction.obj (R := R) (A := A) (B := B) n ⟶
      (ModuleCat.restrictScalars
        (productMap (R := R) (R' := R') (A := A) (B := B) (A' := A') (B' := B')
          aMap bMap)).obj
        (ModuleCat.Tor.TensorAction.obj (R := R') (A := A') (B := B') n) :=
  (ModuleCat.homEquiv
    (M := ModuleCat.Tor.TensorAction.obj (R := R) (A := A) (B := B) n)
    (N := (ModuleCat.restrictScalars
      (productMap (R := R) (R' := R') (A := A) (B := B) (A' := A') (B' := B')
        aMap bMap)).obj
      (ModuleCat.Tor.TensorAction.obj (R := R') (A := A') (B := B') n))).symm
    { toFun := rawAdjointFunction
        (R := R) (R' := R') (A := A) (B := B) (A' := A') (B' := B') hflat aMap bMap n
      map_add' := rawAdjoint_map_add
        (R := R) (R' := R') (A := A) (B := B) (A' := A') (B' := B') hflat aMap bMap n
      map_smul' := rawAdjoint_map_smul
        (R := R) (R' := R') (A := A) (B := B) (A' := A') (B' := B') hflat aMap bMap n }

/-- The canonical source-facing flat base-change comparison for `Tor`. -/
@[stacks 08HW "flat base-change comparison for Tor"]
noncomputable def comparison
    (hflat : (algebraMap R R').Flat)
    (aMap : A ⊗[R] R' →ₐ[R'] A') (bMap : R' ⊗[R] B →ₐ[R'] B') (n : ℕ) :
    (ModuleCat.extendScalars
      (productMap (R := R) (R' := R') (A := A) (B := B) (A' := A') (B' := B')
        aMap bMap)).obj
        (ModuleCat.Tor.TensorAction.obj (R := R) (A := A) (B := B) n) ⟶
      ModuleCat.Tor.TensorAction.obj (R := R') (A := A') (B := B') n :=
  ((ModuleCat.extendRestrictScalarsAdj
    (productMap (R := R) (R' := R') (A := A) (B := B) (A' := A') (B' := B')
      aMap bMap)).homEquiv _ _).symm
    (adjoint (R := R) (R' := R') (A := A) (B := B) (A' := A') (B' := B')
      hflat aMap bMap n)

/-- Lemma 15.61.3 (08HW): the canonical comparison
`Tor_n^R(A, B) ⊗[A ⊗[R] B] (A' ⊗[R'] B') ⟶ Tor_n^{R'}(A', B')`
is an isomorphism when `R'` is flat over `R`, `A'` is flat over
`A ⊗[R] R'`, and `B'` is flat over `R' ⊗[R] B`. -/
@[stacks 08HW "flat base change for Tor"]
theorem comparison_isIso
    [Module.Flat R R']
    (aMap : A ⊗[R] R' →ₐ[R'] A') (bMap : R' ⊗[R] B →ₐ[R'] B') (n : ℕ)
    (haFlat :
      letI : Algebra (A ⊗[R] R') A' := aMap.toAlgebra
      Module.Flat (A ⊗[R] R') A')
    (hbFlat :
      letI : Algebra (R' ⊗[R] B) B' := bMap.toAlgebra
      Module.Flat (R' ⊗[R] B) B') :
    IsIso (comparison (R := R) (R' := R') (A := A) (B := B) (A' := A') (B' := B')
      (RingHom.flat_algebraMap_iff.mpr inferInstance) aMap bMap n) := sorry

end CategoryTheory.ModuleCat.Tor.Flat.BaseChange
