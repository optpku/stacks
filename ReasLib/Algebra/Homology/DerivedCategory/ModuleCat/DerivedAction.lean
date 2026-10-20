/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleEmbedding
public import ReasLib.CategoryTheory.Homology.DoubleComplex.TotalComparison
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Tactic.CrossRefAttribute

/-!
# The regular module action on derived categories

This leaf owns the cochain-level regular-module action and its comparison with the derived tensor
model.

@stack 064M
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.DerivedCategory
open CategoryTheory.MonoidalCategory
open ComplexShape

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.DerivedAction

variable {A : Type u} [CommRing A]

/- The regular-module action is built on the ordinary tensor-complex model.  Keeping this
construction here means that derived users need no chapter-local monoidal structure on the
derived category itself. -/

/-- The degree-zero cochain complex attached to a module. -/
@[stacks 064M "degree-zero cochain complex for the regular action"]
abbrev singleComplex (M : ModuleCat A) : CochainComplex (ModuleCat A) ℤ :=
  (CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj M

/-- Multiplication on the unique surviving first-degree-zero tensor summand. -/
@[stacks 064M "regular-module tensor summand map"]
noncomputable def actionTermMap
    (M : CochainComplex (ModuleCat A) ℤ) (i : ℤ) :
    ((curriedTensor (ModuleCat A)).obj ((singleComplex (ModuleCat.of A A)).X 0)).obj
        (M.X i) ⟶ M.X i :=
  ((HomologicalComplex.singleObjXSelf (up ℤ) (0 : ℤ)
      (ModuleCat.of A A)).hom ⊗ₘ 𝟙 (M.X i)) ≫
    ModuleCat.ofHom (TensorProduct.lid A (M.X i)).toLinearMap

/-- The regular-module action transported along equality of the complex degree. -/
@[stacks 064M "transported regular-module tensor summand map"]
noncomputable def zeroSummandMap
    (M : CochainComplex (ModuleCat A) ℤ) {q i : ℤ} (hqi : q = i) :
    ((curriedTensor (ModuleCat A)).obj ((singleComplex (ModuleCat.of A A)).X 0)).obj
        (M.X q) ⟶ M.X i :=
  eqToHom
      (congrArg
        (fun k ↦
          ((curriedTensor (ModuleCat A)).obj
            ((singleComplex (ModuleCat.of A A)).X 0)).obj (M.X k)) hqi) ≫
    actionTermMap M i

/-- The summand map defining the regular-module action; summands away from degree zero in
`A[0]` are zero. -/
@[stacks 064M "regular-module tensor summand map"]
noncomputable def actionSummandMap
    (M : CochainComplex (ModuleCat A) ℤ) (i p q : ℤ)
    (h : (up ℤ).π (up ℤ) (up ℤ) (p, q) = i) :
    ((curriedTensor (ModuleCat A)).obj ((singleComplex (ModuleCat.of A A)).X p)).obj
        (M.X q) ⟶ M.X i :=
  dite (p = 0)
    (fun hp ↦
      eqToHom
          (congrArg
            (fun k ↦
              ((curriedTensor (ModuleCat A)).obj ((singleComplex (ModuleCat.of A A)).X k)).obj
                (M.X q)) hp) ≫
        zeroSummandMap M (HomologicalComplex₂.ZeroColumn.index_eq hp h))
    (fun _ ↦ 0)

/-- The degreewise component of regular-module tensor action. -/
@[stacks 064M "regular-module tensor action component"]
noncomputable def actionComponent
    (M : CochainComplex (ModuleCat A) ℤ) (i : ℤ) :
    (HomologicalComplex.tensorObj (singleComplex (ModuleCat.of A A)) M).X i ⟶ M.X i :=
  HomologicalComplex.mapBifunctorDesc
    (K₁ := singleComplex (ModuleCat.of A A)) (K₂ := M)
    (F := curriedTensor (ModuleCat A)) (c := up ℤ)
    (A := M.X i) (j := i) (actionSummandMap M i)

/-- The regular-module action components commute with the cochain differential. -/
@[stacks 064M "regular-module tensor action differential compatibility"]
theorem actionComponent_comm
    (M : CochainComplex (ModuleCat A) ℤ) (i j : ℤ) (hij : (up ℤ).Rel i j) :
    actionComponent M i ≫ M.d i j =
      (HomologicalComplex.tensorObj (singleComplex (ModuleCat.of A A)) M).d i j ≫
        actionComponent M j := sorry

/-- The ordinary chain map evaluating `A[0] ⊗ M` by module multiplication. -/
@[stacks 064M "ordinary tensor action on a complex"]
noncomputable def actionMap (M : CochainComplex (ModuleCat A) ℤ) :
    HomologicalComplex.tensorObj (singleComplex (ModuleCat.of A A)) M ⟶ M where
  f i := actionComponent M i
  comm' i j hij := actionComponent_comm M i j hij

/-- The degree-`i` component of `actionMap` is `actionComponent`. -/
@[simp, stacks 064M "regular-module tensor action component formula"]
theorem actionMap_f (M : CochainComplex (ModuleCat A) ℤ) (i : ℤ) :
    (actionMap M).f i = actionComponent M i := sorry

namespace Complex

/-- The derived action of the regular module on a complex representative. -/
@[stacks 064M "derived tensor action on a complex representative"]
noncomputable def derivedAction (M : CochainComplex (ModuleCat A) ℤ) :
    DerivedTensor.Bifunctor.obj (ModuleCat.single0 (ModuleCat.of A A))
        (DerivedCategory.Q.obj M) ⟶ DerivedCategory.Q.obj M :=
  DerivedTensor.Bifunctor.counitAppOfQ (singleComplex (ModuleCat.of A A)) M ≫
    DerivedCategory.Q.map (actionMap M)

/-- The regular-module derived action on a complex representative is invertible. -/
@[stacks 064M "regular-module derived action isomorphism instance"]
noncomputable instance derivedAction_isIso
    (M : CochainComplex (ModuleCat A) ℤ) : IsIso (derivedAction M) := sorry

/-- The regular-module derived action as an isomorphism. -/
@[stacks 064M "derived tensor unit isomorphism on a complex representative"]
noncomputable def derivedActionIso (M : CochainComplex (ModuleCat A) ℤ) :
    DerivedTensor.Bifunctor.obj (ModuleCat.single0 (ModuleCat.of A A))
        (DerivedCategory.Q.obj M) ≅ DerivedCategory.Q.obj M :=
  asIso (derivedAction M)

end Complex

/-- The regular-module derived action on an arbitrary derived object, transported through the
selected complex representative used by `DerivedCategory.Q`. -/
@[stacks 064M "regular-module action on a derived object"]
noncomputable def objectAction (K : DerivedCategory (ModuleCat A)) :
    DerivedTensor.Bifunctor.obj (ModuleCat.single0 (ModuleCat.of A A)) K ⟶ K :=
  let P := (DerivedCategory.Q : CochainComplex (ModuleCat A) ℤ ⥤
    DerivedCategory (ModuleCat A)).objPreimage K
  let e := (DerivedCategory.Q : CochainComplex (ModuleCat A) ℤ ⥤
    DerivedCategory (ModuleCat A)).objObjPreimageIso K
  DerivedTensor.Bifunctor.functor.map (Prod.mkHom (𝟙 _) e.inv) ≫
    Complex.derivedAction P ≫ e.hom

/-- The regular-module derived action on an arbitrary derived object is invertible. -/
@[stacks 064M "regular-module action isomorphism instance"]
noncomputable instance objectAction_isIso (K : DerivedCategory (ModuleCat A)) :
    IsIso (objectAction K) := sorry

/-- The regular-module action on an arbitrary derived object as an isomorphism. -/
@[stacks 064M "regular-module derived action isomorphism"]
noncomputable def objectActionIso (K : DerivedCategory (ModuleCat A)) :
    DerivedTensor.Bifunctor.obj (ModuleCat.single0 (ModuleCat.of A A)) K ≅ K :=
  asIso (objectAction K)

/-- The fixed-right derived tensor of the regular degree-zero module with `K` is canonically
isomorphic to `K`. -/
@[stacks 064M "fixed-right regular-module derived action"]
noncomputable def fixedRightActionIso (K : DerivedCategory (ModuleCat A)) :
    DerivedTensor.Right.obj (ModuleCat.single0 (ModuleCat.of A A)) K ≅ K :=
  DerivedTensor.Bifunctor.Right.isoApp K (ModuleCat.single0 (ModuleCat.of A A)) ≪≫
    objectActionIso K

/-- The derived action of the regular module on a degree-zero module. -/
@[stacks 064M "degree-zero derived tensor action"]
noncomputable def derivedAction (M : ModuleCat A) :
    DerivedTensor.Bifunctor.obj (ModuleCat.single0 (ModuleCat.of A A)) (ModuleCat.single0 M) ⟶
      ModuleCat.single0 M :=
  Complex.derivedAction (singleComplex M)

/-- The degree-zero regular-module derived action is invertible. -/
@[stacks 064M "degree-zero regular-module derived action isomorphism instance"]
noncomputable instance derivedAction_isIso (M : ModuleCat A) :
    IsIso (derivedAction M) := sorry

/-- The degree-zero regular-module action as an isomorphism. -/
@[stacks 064M "degree-zero derived tensor unit isomorphism"]
noncomputable def derivedActionIso (M : ModuleCat A) :
    DerivedTensor.Bifunctor.obj (ModuleCat.single0 (ModuleCat.of A A))
        (ModuleCat.single0 M) ≅ ModuleCat.single0 M :=
  asIso (derivedAction M)

end CategoryTheory.ModuleCat.DerivedAction
