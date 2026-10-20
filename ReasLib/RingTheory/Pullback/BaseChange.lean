/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.TensorProduct.Maps
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Square
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import ReasLib.RingTheory.Pullback.Surjective
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change from a surjective ring pullback

Starting from `B' = B ×_A A'` and a map `B' → D'`, this leaf owns the
three tensor-product base changes `D`, `C'`, and `C`, their commutative
square, and the induced functor between module categories.

@stack 08KK
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Limits.CategoricalPullback
open CategoricalPullback.CatCommSqOver
open scoped TensorProduct

universe u

noncomputable section

variable {B A A' Dp : Type u}
variable [CommRing B] [CommRing A] [CommRing A'] [CommRing Dp]

/-- Situation 15.7.1: a surjective pullback square of rings together with
the ring map `B' → D'` to be base changed. -/
@[stacks 08KK "fiber-product base-change situation"]
structure FiberProductBaseChangeSituation
    extends SurjectiveRingPullbackSituation B A A' where
  /-- The map `B' → D'` used for base change. -/
  bprimeToDp : toSurjectiveRingPullbackSituation.Bprime →+* Dp

namespace FiberProductBaseChangeSituation

local notation "Situation" => @FiberProductBaseChangeSituation B A A' Dp _ _ _ _

/-- The chosen map `B' → D'` supplies the canonical algebra structure on
`D'`. -/
@[stacks 08KK "algebra structure on the chosen target"]
instance instAlgebraBprimeDp (S : Situation) : Algebra S.Bprime Dp :=
  S.bprimeToDp.toAlgebra

/-- The first pullback projection supplies the canonical `B'`-algebra
structure on `B`. -/
@[stacks 08KK "algebra structure from the first pullback projection"]
instance instAlgebraBprimeB (S : Situation) : Algebra S.Bprime B :=
  S.bprimeToB.toAlgebra

/-- The second pullback projection supplies the canonical `B'`-algebra
structure on `A'`. -/
@[stacks 08KK "algebra structure from the second pullback projection"]
instance instAlgebraBprimeAprime (S : Situation) : Algebra S.Bprime A' :=
  S.bprimeToAprime.toAlgebra

/-- The composite through `A'` supplies the canonical `B'`-algebra
structure on `A`. -/
@[stacks 08KK "algebra structure on the common base-change target"]
instance instAlgebraBprimeA (S : Situation) : Algebra S.Bprime A :=
  (S.fromAprime.comp S.bprimeToAprime).toAlgebra

/-- The maps `B' → B → A` form a scalar tower. -/
@[stacks 08KK "first scalar tower in the pullback square"]
theorem bprime_B_A_isScalarTower (S : Situation) :
    let _ : Algebra B A := S.toA.toAlgebra
    IsScalarTower S.Bprime B A := sorry

/-- The maps `B' → A' → A` form a scalar tower. -/
@[stacks 08KK "second scalar tower in the pullback square"]
theorem bprime_Aprime_A_isScalarTower (S : Situation) :
    let _ : Algebra A' A := S.fromAprime.toAlgebra
    IsScalarTower S.Bprime A' A := sorry

/-- The first base change `D = D' ⊗[B'] B`. -/
@[stacks 08KK "first tensor-product base change"]
abbrev D (S : Situation) : Type u :=
  Dp ⊗[S.Bprime] B

/-- The second base change `C' = D' ⊗[B'] A'`. -/
@[stacks 08KK "second tensor-product base change"]
abbrev CPrime (S : Situation) : Type u :=
  Dp ⊗[S.Bprime] A'

/-- The common base change `C = D' ⊗[B'] A`. -/
@[stacks 08KK "common tensor-product base change"]
abbrev C (S : Situation) : Type u :=
  Dp ⊗[S.Bprime] A

/-- The right tensor factor supplies the canonical `B`-algebra structure on
`D`. -/
@[stacks 08KK "algebra structure on the first tensor base change"]
noncomputable instance instAlgebraD (S : Situation) : Algebra B S.D :=
  Algebra.TensorProduct.rightAlgebra

/-- The right tensor factor supplies the canonical `A'`-algebra structure
on `C'`. -/
@[stacks 08KK "algebra structure on the second tensor base change"]
noncomputable instance instAlgebraCPrime (S : Situation) : Algebra A' S.CPrime :=
  Algebra.TensorProduct.rightAlgebra

/-- The left inclusion `D' → D' ⊗[B'] B`. -/
@[stacks 08KK "left inclusion into the first tensor base change"]
abbrev dprimeToD (S : Situation) : Dp →+* S.D :=
  (Algebra.TensorProduct.includeLeft : Dp →ₐ[S.Bprime] S.D).toRingHom

/-- The left inclusion `D' → D' ⊗[B'] A'`. -/
@[stacks 08KK "left inclusion into the second tensor base change"]
abbrev dprimeToCPrime (S : Situation) : Dp →+* S.CPrime :=
  (Algebra.TensorProduct.includeLeft : Dp →ₐ[S.Bprime] S.CPrime).toRingHom

/-- The right inclusion `B → D' ⊗[B'] B`. -/
@[stacks 08KK "right inclusion into the first tensor base change"]
abbrev bToD (S : Situation) : B →+* S.D :=
  (Algebra.TensorProduct.includeRight : B →ₐ[S.Bprime] S.D).toRingHom

/-- The right inclusion `A' → D' ⊗[B'] A'`. -/
@[stacks 08KK "right inclusion into the second tensor base change"]
abbrev aprimeToCPrime (S : Situation) : A' →+* S.CPrime :=
  (Algebra.TensorProduct.includeRight : A' →ₐ[S.Bprime] S.CPrime).toRingHom

/-- The map `D → C` induced by `B → A`. -/
@[stacks 08KK "first map to the common tensor base change"]
abbrev dToC (S : Situation) : S.D →+* S.C :=
  let _ : Algebra B A := S.toA.toAlgebra
  let _ : IsScalarTower S.Bprime B A := bprime_B_A_isScalarTower S
  (Algebra.TensorProduct.map (AlgHom.id S.Bprime Dp)
    (IsScalarTower.toAlgHom S.Bprime B A)).toRingHom

/-- The map `C' → C` induced by `A' → A`. -/
@[stacks 08KK "second map to the common tensor base change"]
abbrev cprimeToC (S : Situation) : S.CPrime →+* S.C :=
  let _ : Algebra A' A := S.fromAprime.toAlgebra
  let _ : IsScalarTower S.Bprime A' A := bprime_Aprime_A_isScalarTower S
  (Algebra.TensorProduct.map (AlgHom.id S.Bprime Dp)
    (IsScalarTower.toAlgHom S.Bprime A' A)).toRingHom

/-- The tensor-product square `D' → D`, `D' → C'`, `D → C`,
`C' → C` is commutative. -/
@[stacks 08KK "commutative tensor-product base-change square"]
theorem tensorSquare (S : Situation) :
    CommSq (CommRingCat.ofHom S.dprimeToD) (CommRingCat.ofHom S.dprimeToCPrime)
      (CommRingCat.ofHom S.dToC) (CommRingCat.ofHom S.cprimeToC) := sorry

/-- The categorical morphism equality underlying the tensor-product
commutative square. -/
theorem tensorSquare_w (S : Situation) :
    CommRingCat.ofHom S.dprimeToD ≫ CommRingCat.ofHom S.dToC =
      CommRingCat.ofHom S.dprimeToCPrime ≫ CommRingCat.ofHom S.cprimeToC := sorry

/-- The ring-hom equality underlying the tensor-product commutative square. -/
@[stacks 08KK "ring-hom form of tensor-square commutativity"]
theorem tensor_square_commutes (S : Situation) :
    S.dToC.comp S.dprimeToD = S.cprimeToC.comp S.dprimeToCPrime := sorry

/-- The canonical map from `D'` to the pullback `D ×_C C'`. -/
@[stacks 08KK "comparison to the tensor-product pullback"]
def tensorPullbackComparison (S : Situation) :
    CommRingCat.of Dp ⟶ pullback (CommRingCat.ofHom S.dToC) (CommRingCat.ofHom S.cprimeToC) :=
  pullback.lift (CommRingCat.ofHom S.dprimeToD)
    (CommRingCat.ofHom S.dprimeToCPrime) (tensorSquare_w S)

/-- The module-category base-change square attached to the tensor square. -/
@[stacks 08KK "module-category base-change square"]
abbrev toModuleCatBaseChangeSquare (S : Situation) :
    CatCommSqOver (ModuleCat.extendScalars S.dToC)
      (ModuleCat.extendScalars S.cprimeToC) (ModuleCat Dp) :=
  ModuleCat.extendScalarsCommSq S.dToC S.cprimeToC S.dprimeToD
    S.dprimeToCPrime S.tensor_square_commutes

/-- The relative module category `Mod_D ×_[Mod_C] Mod_{C'}`. -/
@[stacks 08KK "relative module category of the tensor square"]
abbrev relativeModuleCategory (S : Situation) :=
  CategoricalPullback (ModuleCat.extendScalars.{u, u, u} S.dToC)
    (ModuleCat.extendScalars.{u, u, u} S.cprimeToC)

/-- The canonical functor `Mod_{D'} ⟶ Mod_D ×_[Mod_C] Mod_{C'}`. -/
@[stacks 08KK "relative module functor of the tensor square"]
noncomputable abbrev relativeModuleFunctor (S : Situation) :
    ModuleCat.{u} Dp ⥤ S.relativeModuleCategory :=
  ModuleCat.extendScalarsToPullback.{u} S.dToC S.cprimeToC S.dprimeToD
    S.dprimeToCPrime S.tensor_square_commutes

end FiberProductBaseChangeSituation
