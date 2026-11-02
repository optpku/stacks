/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.RingHom.Smooth
public import ReasLib.RingTheory.Pullback.BaseChange
import Mathlib.Tactic.CrossRefAttribute

/-!
# Descent across a surjective ring pullback

This leaf records the finite-type, flatness, finite-presentation, smoothness,
and étaleness criteria for a system reconstructed from its pullback.  It
also owns the equivalence between flat algebras over `B' = B ×_A A'` and
componentwise-flat algebra systems over `B` and `A'`.

@stack 08KQ
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CommRingCat
open scoped TensorProduct

universe u

noncomputable section

variable {B A A' Dp : Type u}
variable [CommRing B] [CommRing A] [CommRing A'] [CommRing Dp]

namespace FiberProductBaseChangeSituation

local notation "Situation" => @FiberProductBaseChangeSituation B A A' Dp _ _ _ _

/-- Lemma 15.7.7 (1): when `D'` is the pullback of its two base changes,
finite type over `B'` is equivalent to finite type of both components. -/
@[stacks 08KQ "(1) finite-type descent across a surjective pullback"]
theorem finiteType_iff_of_comparison_isIso (S : Situation)
    [IsIso S.tensorPullbackComparison] :
    S.bprimeToDp.FiniteType ↔
      S.bToD.FiniteType ∧ S.aprimeToCPrime.FiniteType := sorry

/-- Lemma 15.7.7 (2): when `D'` is the pullback of its two base changes,
flatness over `B'` is equivalent to flatness of both components. -/
@[stacks 08KQ "(2) flatness descent across a surjective pullback"]
theorem flat_iff_of_comparison_isIso (S : Situation)
    [IsIso S.tensorPullbackComparison] :
    Module.Flat S.Bprime Dp ↔ Module.Flat B S.D ∧ Module.Flat A' S.CPrime := sorry

/-- Lemma 15.7.7 (3): when `D'` is the pullback of its two base changes,
flat finite presentation over `B'` is equivalent to the corresponding
property for both components. -/
@[stacks 08KQ "(3) flat finite-presentation descent across a surjective pullback"]
theorem flat_finitePresentation_iff_of_comparison_isIso (S : Situation)
    [IsIso S.tensorPullbackComparison] :
    (S.bprimeToDp.Flat ∧ S.bprimeToDp.FinitePresentation) ↔
      (S.bToD.Flat ∧ S.bToD.FinitePresentation) ∧
        (S.aprimeToCPrime.Flat ∧ S.aprimeToCPrime.FinitePresentation) := sorry

/-- Lemma 15.7.7 (4): when `D'` is the pullback of its two base changes,
smoothness over `B'` is equivalent to smoothness of both components. -/
@[stacks 08KQ "(4) smoothness descent across a surjective pullback"]
theorem smooth_iff_of_comparison_isIso (S : Situation)
    [IsIso S.tensorPullbackComparison] :
    S.bprimeToDp.Smooth ↔ S.bToD.Smooth ∧ S.aprimeToCPrime.Smooth := sorry

/-- Lemma 15.7.7 (5): when `D'` is the pullback of its two base changes,
étaleness over `B'` is equivalent to étaleness of both components. -/
@[stacks 08KQ "(5) etaleness descent across a surjective pullback"]
theorem etale_iff_of_comparison_isIso (S : Situation)
    [IsIso S.tensorPullbackComparison] :
    S.bprimeToDp.Etale ↔ S.bToD.Etale ∧ S.aprimeToCPrime.Etale := sorry

/-- Lemma 15.7.7 (6): a flat `B'`-algebra is recovered from its two base
changes by the canonical pullback comparison. -/
@[stacks 08KQ "(6) flat algebra is recovered from its pullback system"]
theorem tensorPullbackComparison_isIso_of_flat (S : Situation)
    [Module.Flat S.Bprime Dp] :
    IsIso S.tensorPullbackComparison := by
  letI : Algebra B A := S.toA.toAlgebra
  letI : Algebra A' A := S.fromAprime.toAlgebra
  letI : IsScalarTower S.Bprime A' A := .of_algebraMap_eq' rfl
  letI : IsScalarTower S.Bprime B A := .of_algebraMap_eq' (by
    ext x
    exact congrArg (fun f : S.Bprime ⟶ of A ↦ f x)
      (pullback.condition (f := ofHom S.toA) (g := ofHom S.fromAprime)).symm)
  -- The pullback identifies `B'` with the kernel of the difference map.
  let p : S.Bprime →ₗ[S.Bprime] B × A' :=
    (Algebra.linearMap S.Bprime B).prod (Algebra.linearMap S.Bprime A')
  let q : B × A' →ₗ[S.Bprime] A :=
    (IsScalarTower.toAlgHom S.Bprime B A).toLinearMap.comp (LinearMap.fst _ _ _) -
      (IsScalarTower.toAlgHom S.Bprime A' A).toLinearMap.comp (LinearMap.snd _ _ _)
  have hpb := (IsPullback.of_hasPullback (ofHom S.toA) (ofHom S.fromAprime)).map
    (forget CommRingCat)
  have hp : Function.Injective p := by
    intro x y h
    exact Types.ext_of_isPullback hpb (congrArg Prod.fst h) (congrArg Prod.snd h)
  have hpq : Function.Exact p q := by
    intro x
    change S.toA x.1 - S.fromAprime x.2 = 0 ↔ ∃ r, p r = x
    rw [sub_eq_zero]
    constructor
    · intro hx
      obtain ⟨r, hr, hr'⟩ := Types.exists_of_isPullback hpb x.1 x.2 hx
      exact ⟨r, Prod.ext hr hr'⟩
    · rintro ⟨r, rfl⟩
      exact congrArg (fun f : S.Bprime ⟶ of A ↦ f r)
        (pullback.condition (f := ofHom S.toA) (g := ofHom S.fromAprime))
  -- Tensoring this exact pair with the flat module `D'` preserves exactness.
  let e := TensorProduct.prodRight S.Bprime S.Bprime Dp B A'
  let r := TensorProduct.rid S.Bprime Dp
  let t : Dp →ₗ[S.Bprime] S.D × S.CPrime :=
    e.toLinearMap.comp ((p.lTensor Dp).comp r.symm.toLinearMap)
  have ht (d : Dp) : t d = (S.dprimeToD d, S.dprimeToCPrime d) := by
    simp [t, e, r, p, dprimeToD, dprimeToCPrime]
  have hq (x : Dp ⊗[S.Bprime] (B × A')) :
      q.lTensor Dp x = S.dToC (e x).1 - S.cprimeToC (e x).2 := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul d x => simp [q, e, dToC, cprimeToC]
    | add x y hx hy => simp [map_add, hx, hy, sub_add_sub_comm]
  have ht_inj : Function.Injective t :=
    e.injective.comp ((Module.Flat.lTensor_preserves_injective_linearMap p hp).comp
      r.symm.injective)
  have hcomp (d : Dp) :
      ((pullback.fst (ofHom S.dToC) (ofHom S.cprimeToC))
          (S.tensorPullbackComparison d),
        (pullback.snd (ofHom S.dToC) (ofHom S.cprimeToC))
          (S.tensorPullbackComparison d)) = t d := by
    rw [ht]
    exact Prod.ext
      (congrArg (fun f : of Dp ⟶ of S.D ↦ f d) (pullback.lift_fst _ _ _))
      (congrArg (fun f : of Dp ⟶ of S.CPrime ↦ f d) (pullback.lift_snd _ _ _))
  -- The resulting bijection is the prescribed ring pullback comparison.
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro x y hxy
    apply ht_inj
    rw [← hcomp x, ← hcomp y, hxy]
  · intro z
    let x := (pullback.fst (ofHom S.dToC) (ofHom S.cprimeToC)) z
    let y := (pullback.snd (ofHom S.dToC) (ofHom S.cprimeToC)) z
    have hz : q.lTensor Dp (e.symm (x, y)) = 0 := by
      rw [hq, e.apply_symm_apply, sub_eq_zero]
      exact congrArg (fun f : pullback (ofHom S.dToC) (ofHom S.cprimeToC) ⟶ of S.C ↦
        f z) (pullback.condition (f := ofHom S.dToC) (g := ofHom S.cprimeToC))
    obtain ⟨w, hw⟩ := (Module.Flat.lTensor_exact Dp hpq (e.symm (x, y))).mp hz
    have hw' : t (r w) = (x, y) := by
      change e ((p.lTensor Dp) (r.symm (r w))) = (x, y)
      rw [r.symm_apply_apply, hw, e.apply_symm_apply]
    refine ⟨r w, ?_⟩
    apply Types.ext_of_isPullback
      ((IsPullback.of_hasPullback (ofHom S.dToC) (ofHom S.cprimeToC)).map
        (forget CommRingCat))
    · exact congrArg Prod.fst ((hcomp (r w)).trans hw')
    · exact congrArg Prod.snd ((hcomp (r w)).trans hw')

end FiberProductBaseChangeSituation

namespace SurjectiveRingPullbackSituation

local notation "Situation" => @SurjectiveRingPullbackSituation B A A' _ _ _

/-- The object property on `Under B'` selecting flat `B'`-algebras. -/
@[stacks 08KQ "flat algebra object property"]
abbrev flatAlgebraProperty (S : Situation) : ObjectProperty (Under S.Bprime) :=
  fun D' ↦ D'.hom.hom.Flat

/-- The full subcategory of flat algebras over `B' = B ×_A A'`. -/
@[stacks 08KQ "category of flat algebras over the pullback"]
abbrev FlatAlgebraCat (S : Situation) :=
  (flatAlgebraProperty S).FullSubcategory

/-- The category of systems consisting of a `B`-algebra, an `A'`-algebra,
and an isomorphism between their base changes to `A`. -/
@[stacks 08KQ "category of algebra gluing systems"]
abbrev algebraSystemCategory (S : Situation) :=
  let _ : Algebra B A := S.toA.toAlgebra
  let _ : Algebra A' A := S.fromAprime.toAlgebra
  CategoricalPullback (Under.pushout (ofHom S.toA))
    (Under.pushout (ofHom S.fromAprime))

/-- The first component of an algebra system has its canonical `B`-algebra
structure. -/
@[stacks 08KQ "algebra structure on the first system component"]
noncomputable instance instAlgebraSystemFst
    (S : Situation) (X : algebraSystemCategory S) : Algebra B X.fst.right :=
  X.fst.hom.hom.toAlgebra

/-- The second component of an algebra system has its canonical
`A'`-algebra structure. -/
@[stacks 08KQ "algebra structure on the second system component"]
noncomputable instance instAlgebraSystemSnd
    (S : Situation) (X : algebraSystemCategory S) : Algebra A' X.snd.right :=
  X.snd.hom.hom.toAlgebra

/-- The object property on algebra systems requiring both components to be
flat over their respective base rings. -/
@[stacks 08KQ "componentwise-flat algebra-system property"]
abbrev flatAlgebraSystemProperty (S : Situation) :
    ObjectProperty (algebraSystemCategory S) :=
  fun X ↦ X.fst.hom.hom.Flat ∧ X.snd.hom.hom.Flat

/-- The full subcategory of componentwise-flat algebra systems. -/
@[stacks 08KQ "category of componentwise-flat algebra systems"]
abbrev FlatAlgebraSystemCat (S : Situation) :=
  (flatAlgebraSystemProperty S).FullSubcategory

/-- The two composites `B' → B → A` and `B' → A' → A` agree in
`CommRingCat`. -/
theorem pushoutSquare_commutes (S : Situation) :
    ofHom S.bprimeToB ≫ ofHom S.toA =
      ofHom S.bprimeToAprime ≫ ofHom S.fromAprime := by
  exact pullback.condition

/-- The comparison between the two iterated pushout functors from
`B'`-algebras to `A`-algebras. -/
@[stacks 08KQ "iterated base-change comparison"]
def algebraBaseChangeComparison (S : Situation) :
    let bprimeToB : S.Bprime ⟶ of B := ofHom S.bprimeToB
    let bprimeToAprime : S.Bprime ⟶ of A' := ofHom S.bprimeToAprime
    Under.pushout bprimeToB ⋙ Under.pushout (ofHom S.toA) ≅
      Under.pushout bprimeToAprime ⋙ Under.pushout (ofHom S.fromAprime) :=
  let bprimeToB : S.Bprime ⟶ of B := ofHom S.bprimeToB
  let bprimeToAprime : S.Bprime ⟶ of A' := ofHom S.bprimeToAprime
  (Under.pushoutComp bprimeToB (ofHom S.toA)).symm ≪≫
    eqToIso (congrArg (fun f ↦ Under.pushout f) (pushoutSquare_commutes S)) ≪≫
    Under.pushoutComp bprimeToAprime (ofHom S.fromAprime)

/-- The categorical square of pushout functors attached to the surjective
ring pullback. -/
@[stacks 08KQ "base-change square for algebra systems"]
def algebraBaseChangeSquare (S : Situation) :
    CategoricalPullback.CatCommSqOver (Under.pushout (ofHom S.toA))
      (Under.pushout (ofHom S.fromAprime)) (Under S.Bprime) where
  fst := Under.pushout (ofHom S.bprimeToB)
  snd := Under.pushout (ofHom S.bprimeToAprime)
  iso := algebraBaseChangeComparison S

/-- The canonical functor from `B'`-algebras to algebra systems. -/
@[stacks 08KQ "base-change functor to algebra systems"]
def algebraBaseChangeFunctor (S : Situation) :
    Under S.Bprime ⥤ algebraSystemCategory S :=
  (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
    (Under.pushout (ofHom S.toA)) (Under.pushout (ofHom S.fromAprime))
    (Under S.Bprime)).obj (algebraBaseChangeSquare S)

/-- Base change sends a flat `B'`-algebra to a componentwise-flat algebra
system. -/
theorem algebraBaseChange_obj_mem_flatAlgebraSystemProperty
    (S : Situation) ⦃D' : Under S.Bprime⦄
    (hflat : flatAlgebraProperty S D') :
    flatAlgebraSystemProperty S ((algebraBaseChangeFunctor S).obj D') := by
  constructor
  · exact CommRingCat.flat.pushout_inr D'.hom (ofHom S.bprimeToB) hflat
  · exact CommRingCat.flat.pushout_inr D'.hom (ofHom S.bprimeToAprime) hflat

/-- The canonical base-change functor on the flat full subcategories. -/
@[stacks 08KQ "base-change functor on flat algebra subcategories"]
abbrev flatAlgebraBaseChangeFunctor (S : Situation) :
    FlatAlgebraCat S ⥤ FlatAlgebraSystemCat S :=
  (flatAlgebraSystemProperty S).lift
    ((flatAlgebraProperty S).ι ⋙ algebraBaseChangeFunctor S)
    (fun D' ↦ algebraBaseChange_obj_mem_flatAlgebraSystemProperty S D'.property)

/-- Lemma 15.7.7 (7): flat `B'`-algebras are equivalent to
componentwise-flat algebra systems over `B` and `A'`. -/
@[stacks 08KQ "(7) equivalence of flat algebra gluing systems"]
theorem flatAlgebraBaseChangeFunctor_isEquivalence (S : Situation) :
    Functor.IsEquivalence (flatAlgebraBaseChangeFunctor S) := sorry

end SurjectiveRingPullbackSituation
