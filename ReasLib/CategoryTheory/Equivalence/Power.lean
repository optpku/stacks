/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Shift.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Endofunctor.Iteration.Natural

/-!
# Integral powers of autoequivalences

Mathlib defines integer powers of an autoequivalence, but does not yet provide the natural
comparison between consecutive powers. This file supplies the zero, successor, predecessor, and
degree-transport interfaces without installing a noncanonical global `HasShift` instance.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.Equivalence

variable {C : Type u} [Category.{v} C]

/-- Transport powers of an autoequivalence along an equality of their integer exponents. -/
noncomputable def powIndexIso
    (e : C ≌ C) {m n : ℤ} (h : m = n) :
    (e ^ m).functor ≅ (e ^ n).functor :=
  eqToIso (congrArg (fun k : ℤ ↦ (e ^ k).functor) h)

/-- Consecutive transports of the exponent compose to the direct transport. -/
@[reassoc, stacks 01CU "composition of exponent transports"]
theorem powIndexIso_trans
    (e : C ≌ C) {m n p : ℤ} (h : m = n) (k : n = p) :
    powIndexIso e h ≪≫ powIndexIso e k = powIndexIso e (h.trans k) := by
  cases h
  cases k
  simp [powIndexIso]

/-- Transport the orbit of an object under powers of an autoequivalence along an equality of
exponents. -/
noncomputable def powObjIndexIso
    (e : C ≌ C) (A : C) {m n : ℤ} (h : m = n) :
    (e ^ m).functor.obj A ≅ (e ^ n).functor.obj A :=
  (powIndexIso e h).app A

/-- Powers of an autoequivalence preserve isomorphisms between base objects. -/
noncomputable def powObjMapIso
    (e : C ≌ C) {A B : C} (f : A ≅ B) (n : ℤ) :
    (e ^ n).functor.obj A ≅ (e ^ n).functor.obj B :=
  (e ^ n).functor.mapIso f

/-- The zeroth power of an autoequivalence is the identity functor. -/
@[stacks 01CU "zeroth power of an autoequivalence"]
noncomputable def powZeroIso (e : C ≌ C) :
    (e ^ (0 : ℤ)).functor ≅ 𝟭 C :=
  Iso.refl _

/-- The forward component of the zero-power comparison is the identity. -/
@[simp, stacks 01CU "zero-power comparison hom component"]
theorem powZeroIso_hom_app (e : C ≌ C) (A : C) :
    (powZeroIso e).hom.app A = 𝟙 A := rfl

/-- The inverse component of the zero-power comparison is the identity. -/
@[simp, stacks 01CU "zero-power comparison inverse component"]
theorem powZeroIso_inv_app (e : C ≌ C) (A : C) :
    (powZeroIso e).inv.app A = 𝟙 A := rfl

namespace PowAux

/-- Left composition by the zero power is canonically trivial. -/
@[stacks 01CU "left composition by the zero power"]
noncomputable def powZeroLeftIso (e : C ≌ C) (F : C ⥤ C) :
    F ≅ (e ^ (0 : ℤ)).functor ⋙ F :=
  (Functor.leftUnitor F).symm ≪≫
    Functor.isoWhiskerRight (powZeroIso e).symm F

set_option backward.isDefEq.respectTransparency false in
/-- The zero-power left-composition comparison is natural in the endofunctor. -/
@[reassoc, stacks 01CU "naturality of left composition by the zero power"]
theorem powZeroLeftIso_naturality
    (e : C ≌ C) {F G : C ⥤ C} (α : F ≅ G) :
    α ≪≫ powZeroLeftIso e G =
      powZeroLeftIso e F ≪≫
        Functor.isoWhiskerLeft (e ^ (0 : ℤ)).functor α := by
  apply Iso.ext
  ext A
  simp [powZeroLeftIso]
  change α.hom.app A = 𝟙 _ ≫ α.hom.app A
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The zero-power left-composition comparison is compatible with right composition. -/
@[reassoc, stacks 01CU "zero-power left comparison and right composition"]
theorem powZeroLeftIso_comp (e : C ≌ C) (F G : C ⥤ C) :
    Functor.isoWhiskerRight (powZeroLeftIso e F) G ≪≫
        Functor.associator (e ^ (0 : ℤ)).functor F G =
      powZeroLeftIso e (F ⋙ G) := by
  apply Iso.ext
  ext A
  simp [powZeroLeftIso]
  exact Category.id_comp _

/-- Conjugating the zero-power left-composition comparison by an isomorphism is trivial. -/
@[reassoc, stacks 01CU "conjugation of the zero-power left comparison"]
theorem powZeroLeftIso_conj
    (e : C ≌ C) {F G : C ⥤ C} (α : F ≅ G) :
    α.symm ≪≫ powZeroLeftIso e F ≪≫
        Functor.isoWhiskerLeft (e ^ (0 : ℤ)).functor α =
      powZeroLeftIso e G := by
  rw [← powZeroLeftIso_naturality e α]
  simp

end PowAux

namespace Iterate

/-- The shared zero-based iterate of the functor underlying an autoequivalence agrees with its
nonnegative integer power. -/
@[stacks 01CU "endofunctor iterate and autoequivalence power"]
theorem eq_pow (e : C ≌ C) (n : ℕ) :
    Endofunctor.iterate e.functor n = (e ^ (n : ℤ)).functor := by
  have succ_left (k : ℕ) :
      Endofunctor.iterate e.functor (k + 1) =
        e.functor ⋙ Endofunctor.iterate e.functor k := by
    induction k with
    | zero => rfl
    | succ k ih =>
        change Endofunctor.iterate e.functor (k + 1) ⋙ e.functor =
          e.functor ⋙ (Endofunctor.iterate e.functor k ⋙ e.functor)
        rw [ih]
        rfl
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [succ_left n, ih]
      cases n <;> rfl

/-- Evaluating the zero-based iterate of an autoequivalence on an object agrees with evaluating
its nonnegative integer power. -/
@[stacks 01CU "objectwise endofunctor iterate and autoequivalence power"]
theorem obj_eq_pow (e : C ≌ C) (A : C) (n : ℕ) :
    (Endofunctor.iterate e.functor n).obj A = (e ^ (n : ℤ)).functor.obj A :=
  congrArg (fun F : C ⥤ C ↦ F.obj A) (eq_pow e n)

/-- The zero-based iterate of the inverse functor of an autoequivalence agrees with the
corresponding negative integer power. -/
@[stacks 01CU "inverse endofunctor iterate and autoequivalence power"]
theorem inverse_eq_pow_neg (e : C ≌ C) (n : ℕ) :
    Endofunctor.iterate e.inverse n = (e ^ (-(n : ℤ))).functor := by
  change Endofunctor.iterate e.symm.functor n = _
  rw [eq_pow e.symm n]
  cases n <;> rfl

/-- Evaluating the zero-based iterate of the inverse functor agrees with evaluating the
corresponding negative integer power. -/
@[stacks 01CU "objectwise inverse endofunctor iterate and autoequivalence power"]
theorem inverse_obj_eq_pow_neg (e : C ≌ C) (A : C) (n : ℕ) :
    (Endofunctor.iterate e.inverse n).obj A = (e ^ (-(n : ℤ))).functor.obj A :=
  congrArg (fun F : C ⥤ C ↦ F.obj A) (inverse_eq_pow_neg e n)

end Iterate

namespace PowAux

/-- Object-level bookkeeping for a nonnegative successor power. -/
theorem rightSuccOfNatObj (e : C ≌ C) (A : C) (n : ℕ) :
    e.functor.obj ((e ^ (n : ℤ)).functor.obj A) =
      (e ^ ((n : ℤ) + 1)).functor.obj A := by
  rw [← Iterate.obj_eq_pow e A n]
  have h : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by omega
  rw [h, ← Iterate.obj_eq_pow e A (n + 1)]
  rfl

/-- Object-level source bookkeeping for cancelling the leading inverse in a negative power. -/
theorem rightSuccNegSuccSource (e : C ≌ C) (A : C) (n : ℕ) :
    e.functor.obj ((e ^ Int.negSucc (n + 1)).functor.obj A) =
      e.functor.obj (e.inverse.obj ((e ^ Int.negSucc n).functor.obj A)) := by
  have hn : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := by omega
  have hn1 : Int.negSucc (n + 1) = -((n + 2 : ℕ) : ℤ) := by omega
  rw [hn1, ← Iterate.inverse_obj_eq_pow_neg e A (n + 2)]
  rw [hn, ← Iterate.inverse_obj_eq_pow_neg e A (n + 1)]
  rfl

/-- Object-level target bookkeeping for a negative successor power. -/
theorem rightSuccNegSuccTarget (e : C ≌ C) (A : C) (n : ℕ) :
    (e ^ Int.negSucc n).functor.obj A =
      (e ^ (Int.negSucc (n + 1) + 1)).functor.obj A := by
  have h : Int.negSucc (n + 1) + 1 = Int.negSucc n := by omega
  rw [h]

/-- Every integer exponent is the successor of its predecessor. -/
theorem predSucc (n : ℤ) : n = (n - 1) + 1 := by omega

/-- Casting a natural-number successor agrees with adding one in `ℤ`. -/
theorem ofNatSucc (n : ℕ) :
    (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by omega

/-- Adding a positive successor may be reassociated as a successor after addition. -/
theorem addOfNatSucc (m : ℤ) (n : ℕ) :
    m + ((n + 1 : ℕ) : ℤ) = (m + (n : ℤ)) + 1 := by omega

/-- Adding `-1` agrees with taking the predecessor. -/
theorem addNegOne (m : ℤ) : m + Int.negSucc 0 = m - 1 := by omega

/-- Taking the predecessor of a negative successor gives the next negative successor. -/
theorem negSuccPred (n : ℕ) :
    Int.negSucc n - 1 = Int.negSucc (n + 1) := by omega

/-- Adding a further negative successor may be reassociated as a predecessor after addition. -/
theorem addNegSucc (m : ℤ) (n : ℕ) :
    m + Int.negSucc (n + 1) = (m + Int.negSucc n) - 1 := by omega

end PowAux

/-- The objectwise comparison between applying an autoequivalence after its `n`th power and its
`(n + 1)`st power. -/
@[stacks 01CU "successor component for powers of an autoequivalence"]
noncomputable def powRightSuccApp (e : C ≌ C) (A : C) :
    (n : ℤ) →
      e.functor.obj ((e ^ n).functor.obj A) ≅ (e ^ (n + 1)).functor.obj A
  | .ofNat n => eqToIso (PowAux.rightSuccOfNatObj e A n)
  | .negSucc 0 => e.counitIso.app A
  | .negSucc (n + 1) =>
      eqToIso (PowAux.rightSuccNegSuccSource e A n) ≪≫
        e.counitIso.app ((e ^ Int.negSucc n).functor.obj A) ≪≫
        eqToIso (PowAux.rightSuccNegSuccTarget e A n)

set_option backward.isDefEq.respectTransparency false in
/-- The successor components are natural in the object. -/
theorem powRightSuccApp_naturality
    (e : C ≌ C) (n : ℤ) {A B : C} (f : A ⟶ B) :
    (((e ^ n).functor ⋙ e.functor).map f :
        ((e ^ n).functor ⋙ e.functor).obj A ⟶
          ((e ^ n).functor ⋙ e.functor).obj B) ≫
        (powRightSuccApp e B n).hom =
      (powRightSuccApp e A n).hom ≫
        ((e ^ (n + 1)).functor.map f :
          (e ^ (n + 1)).functor.obj A ⟶ (e ^ (n + 1)).functor.obj B) := by
  rcases n with n | n
  · have hn : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by omega
    let h : (e ^ (n : ℤ)).functor ⋙ e.functor =
        (e ^ ((n : ℤ) + 1)).functor := by
      rw [hn, ← Iterate.eq_pow e n, ← Iterate.eq_pow e (n + 1)]
      rfl
    simpa only [Int.ofNat_eq_natCast, powRightSuccApp, eqToIso.hom,
      Iso.app_hom, eqToHom_app] using
      (eqToIso h).hom.naturality f
  · cases n with
    | zero =>
        change e.functor.map (e.inverse.map f) ≫ e.counitIso.hom.app B =
          e.counitIso.hom.app A ≫ f
        exact e.counitIso.hom.naturality f
    | succ n =>
        let p : ℤ := Int.negSucc n
        let q : ℤ := Int.negSucc (n + 1)
        have hp : p = -((n + 1 : ℕ) : ℤ) := by omega
        have hq : q = -((n + 2 : ℕ) : ℤ) := by omega
        have hqp : q + 1 = p := by omega
        let hs : (e ^ q).functor = (e ^ p).functor ⋙ e.inverse := by
          rw [hq, ← Iterate.inverse_eq_pow_neg e (n + 2)]
          rw [hp, ← Iterate.inverse_eq_pow_neg e (n + 1)]
          rfl
        let hs' : (e ^ q).functor ⋙ e.functor =
            (e ^ p).functor ⋙ (e.inverse ⋙ e.functor) := by
          rw [hs]
          rfl
        let ht : (e ^ p).functor = (e ^ (q + 1)).functor :=
          congrArg (fun i : ℤ ↦ (e ^ i).functor) hqp.symm
        let ht' : (e ^ p).functor ⋙ 𝟭 C = (e ^ (q + 1)).functor := by
          rw [Functor.comp_id]
          exact ht
        let ι : (e ^ q).functor ⋙ e.functor ≅ (e ^ (q + 1)).functor :=
          eqToIso hs' ≪≫
            Functor.isoWhiskerLeft (e ^ p).functor e.counitIso ≪≫
            eqToIso ht'
        change ((e ^ q).functor ⋙ e.functor).map f ≫
            (powRightSuccApp e B q).hom =
          (powRightSuccApp e A q).hom ≫ (e ^ (q + 1)).functor.map f
        simpa [ι, p, q, powRightSuccApp, hs', ht', Functor.comp_map,
          Category.assoc] using ι.hom.naturality f

/-- The forward natural transformation whose components are the successor comparisons. -/
@[stacks 01CU "successor natural transformation for powers of an autoequivalence"]
noncomputable def powRightSuccNatTrans (e : C ≌ C) (n : ℤ) :
    (e ^ n).functor ⋙ e.functor ⟶ (e ^ (n + 1)).functor where
  app A := (powRightSuccApp e A n).hom
  naturality _ _ f := powRightSuccApp_naturality e n f

/-- A component of `powRightSuccNatTrans` is the forward successor comparison. -/
@[simp, stacks 01CU "successor natural transformation component"]
theorem powRightSuccNatTrans_app (e : C ≌ C) (n : ℤ) (A : C) :
    (powRightSuccNatTrans e n).app A = (powRightSuccApp e A n).hom := rfl

/-- The named inverse of an objectwise successor comparison. -/
@[stacks 01CU "successor component inverse for powers of an autoequivalence"]
noncomputable def powRightSuccAppInv (e : C ≌ C) (A : C) (n : ℤ) :
    (e ^ (n + 1)).functor.obj A ⟶
      e.functor.obj ((e ^ n).functor.obj A) :=
  (powRightSuccApp e A n).inv

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the inverse successor comparison in the object variable. -/
@[stacks 01CU "successor component inverse naturality"]
theorem powRightSuccAppInv_naturality
    (e : C ≌ C) (n : ℤ) {A B : C} (f : A ⟶ B) :
    (e ^ (n + 1)).functor.map f ≫ powRightSuccAppInv e B n =
      powRightSuccAppInv e A n ≫ ((e ^ n).functor ⋙ e.functor).map f := by
  rw [eq_comm]
  change (powRightSuccApp e A n).inv ≫
      ((e ^ n).functor ⋙ e.functor).map f =
    (e ^ (n + 1)).functor.map f ≫ (powRightSuccApp e B n).inv
  rw [(powRightSuccApp e A n).inv_comp_eq]
  rw [Functor.comp_map]
  rw [← Category.assoc, (powRightSuccApp e B n).eq_comp_inv]
  exact powRightSuccApp_naturality e n f

/-- The inverse natural transformation whose components are the inverse successor comparisons. -/
@[stacks 01CU "inverse successor natural transformation for powers of an autoequivalence"]
noncomputable def powRightSuccNatTransInv (e : C ≌ C) (n : ℤ) :
    (e ^ (n + 1)).functor ⟶ (e ^ n).functor ⋙ e.functor where
  app A := powRightSuccAppInv e A n
  naturality _ _ f := powRightSuccAppInv_naturality e n f

/-- The inverse natural transformation satisfies the successor naturality equation. -/
@[stacks 01CU "inverse successor natural transformation naturality"]
theorem powRightSuccNatTransInv_naturality
    (e : C ≌ C) (n : ℤ) {A B : C} (f : A ⟶ B) :
    (e ^ (n + 1)).functor.map f ≫
        (powRightSuccNatTransInv e n).app B =
      (powRightSuccNatTransInv e n).app A ≫
        ((e ^ n).functor ⋙ e.functor).map f :=
  powRightSuccAppInv_naturality e n f

/-- A component of `powRightSuccNatTransInv` is the named inverse comparison. -/
@[simp, stacks 01CU "inverse successor natural transformation component"]
theorem powRightSuccNatTransInv_app (e : C ≌ C) (n : ℤ) (A : C) :
    (powRightSuccNatTransInv e n).app A = powRightSuccAppInv e A n := rfl

/-- A successor comparison followed by its named inverse is the identity. -/
@[simp, stacks 01CU "successor component hom-inverse law"]
theorem powRightSuccApp_hom_comp_inv (e : C ≌ C) (n : ℤ) (A : C) :
    (powRightSuccApp e A n).hom ≫ powRightSuccAppInv e A n = 𝟙 _ := by
  simp [powRightSuccAppInv]

/-- The named inverse of a successor comparison followed by the comparison is the identity. -/
@[simp, stacks 01CU "successor component inverse-hom law"]
theorem powRightSuccApp_inv_comp_hom (e : C ≌ C) (n : ℤ) (A : C) :
    powRightSuccAppInv e A n ≫ (powRightSuccApp e A n).hom = 𝟙 _ := by
  simp [powRightSuccAppInv]

/-- The forward and inverse successor natural transformations compose to the identity. -/
@[simp, stacks 01CU "successor natural transformation forward-inverse law"]
theorem powRightSuccNatTrans_hom_inv_id (e : C ≌ C) (n : ℤ) :
    powRightSuccNatTrans e n ≫ powRightSuccNatTransInv e n = 𝟙 _ := by
  ext A
  simp [powRightSuccNatTrans, powRightSuccNatTransInv, powRightSuccAppInv]

/-- The inverse and forward successor natural transformations compose to the identity. -/
@[simp, stacks 01CU "successor natural transformation inverse-forward law"]
theorem powRightSuccNatTrans_inv_hom_id (e : C ≌ C) (n : ℤ) :
    powRightSuccNatTransInv e n ≫ powRightSuccNatTrans e n = 𝟙 _ := by
  ext A
  simp [powRightSuccNatTrans, powRightSuccNatTransInv, powRightSuccAppInv]

/-- The forward and inverse successor components compose to the identity. -/
@[simp, stacks 01CU "successor component forward-inverse law"]
theorem powRightSuccNatTrans_app_comp_inv_app (e : C ≌ C) (n : ℤ) (A : C) :
    (powRightSuccNatTrans e n).app A ≫
        (powRightSuccNatTransInv e n).app A = 𝟙 _ := by
  simp [powRightSuccNatTrans, powRightSuccNatTransInv, powRightSuccAppInv]

/-- The inverse and forward successor components compose to the identity. -/
@[simp, stacks 01CU "successor component inverse-forward law"]
theorem powRightSuccNatTransInv_app_comp_app (e : C ≌ C) (n : ℤ) (A : C) :
    (powRightSuccNatTransInv e n).app A ≫
        (powRightSuccNatTrans e n).app A = 𝟙 _ := by
  simp [powRightSuccNatTrans, powRightSuccNatTransInv, powRightSuccAppInv]

/-- Composing the `n`th power of an autoequivalence with the autoequivalence itself gives its
`(n + 1)`st power. -/
@[stacks 01CU "successor comparison for powers of an autoequivalence"]
noncomputable def powRightSuccIso (e : C ≌ C) (n : ℤ) :
    (e ^ n).functor ⋙ e.functor ≅ (e ^ (n + 1)).functor :=
  { hom := powRightSuccNatTrans e n
    inv := powRightSuccNatTransInv e n
    hom_inv_id := powRightSuccNatTrans_hom_inv_id e n
    inv_hom_id := powRightSuccNatTrans_inv_hom_id e n }

/-- The forward natural transformation of `powRightSuccIso`. -/
@[simp, stacks 01CU "successor comparison natural transformation hom"]
theorem powRightSuccIso_hom (e : C ≌ C) (n : ℤ) :
    (powRightSuccIso e n).hom = powRightSuccNatTrans e n := rfl

/-- The inverse natural transformation of `powRightSuccIso`. -/
@[simp, stacks 01CU "successor comparison natural transformation inverse"]
theorem powRightSuccIso_inv (e : C ≌ C) (n : ℤ) :
    (powRightSuccIso e n).inv = powRightSuccNatTransInv e n := rfl

/-- The objectwise isomorphism supplied by `powRightSuccIso`. -/
@[simp, stacks 01CU "successor comparison objectwise isomorphism"]
theorem powRightSuccIso_app (e : C ≌ C) (n : ℤ) (A : C) :
    (powRightSuccIso e n).app A = powRightSuccApp e A n := by
  ext
  rfl

/-- The forward component of `powRightSuccIso`. -/
@[simp, stacks 01CU "successor comparison hom component"]
theorem powRightSuccIso_hom_app (e : C ≌ C) (n : ℤ) (A : C) :
    (powRightSuccIso e n).hom.app A = (powRightSuccApp e A n).hom := rfl

/-- The inverse component of `powRightSuccIso`. -/
@[simp, stacks 01CU "successor comparison inverse component"]
theorem powRightSuccIso_inv_app (e : C ≌ C) (n : ℤ) (A : C) :
    (powRightSuccIso e n).inv.app A = powRightSuccAppInv e A n := rfl

/-- The successor comparison commutes with transport of its integer index. -/
@[reassoc, stacks 01CU "successor comparison and index transport"]
theorem powRightSuccIso_hom_naturality_index
    (e : C ≌ C) {m n : ℤ} (h : m = n) :
    (Functor.isoWhiskerRight (powIndexIso e h) e.functor).hom ≫
        (powRightSuccIso e n).hom =
      (powRightSuccIso e m).hom ≫
        (powIndexIso e (congrArg (fun k : ℤ ↦ k + 1) h)).hom := by
  subst n
  simp [powIndexIso]

/-- The inverse successor comparison commutes with transport of its integer index. -/
@[reassoc, stacks 01CU "inverse successor comparison and index transport"]
theorem powRightSuccIso_inv_naturality_index
    (e : C ≌ C) {m n : ℤ} (h : m = n) :
    (powIndexIso e (congrArg (fun k : ℤ ↦ k + 1) h)).hom ≫
        (powRightSuccIso e n).inv =
      (powRightSuccIso e m).inv ≫
        (Functor.isoWhiskerRight (powIndexIso e h) e.functor).hom := by
  subst n
  simp [powIndexIso]

/-- The symmetric successor comparison commutes with transport of its integer index. -/
@[reassoc, stacks 01CU "symmetric successor comparison and index transport"]
theorem powRightSuccIso_symm_naturality_index
    (e : C ≌ C) {m n : ℤ} (h : m = n) :
    (powRightSuccIso e m).symm ≪≫
        Functor.isoWhiskerRight (powIndexIso e h) e.functor =
      powIndexIso e (congrArg (fun k : ℤ ↦ k + 1) h) ≪≫
        (powRightSuccIso e n).symm := by
  apply Iso.ext
  exact (powRightSuccIso_inv_naturality_index e h).symm

/-- Composing the `n`th power of an autoequivalence with its inverse gives the predecessor power. -/
@[stacks 01CU "predecessor comparison for powers of an autoequivalence"]
noncomputable def powRightPredIso (e : C ≌ C) (n : ℤ) :
    (e ^ n).functor ⋙ e.inverse ≅ (e ^ (n - 1)).functor :=
  Functor.isoWhiskerRight (powIndexIso e (PowAux.predSucc n)) e.inverse ≪≫
    Functor.isoWhiskerRight (powRightSuccIso e (n - 1)).symm e.inverse ≪≫
    Functor.associator (e ^ (n - 1)).functor e.functor e.inverse ≪≫
    Functor.isoWhiskerLeft (e ^ (n - 1)).functor e.unitIso.symm ≪≫
    Functor.rightUnitor (e ^ (n - 1)).functor

/-- The symmetric predecessor comparison commutes with transport of its integer index. -/
@[reassoc, stacks 01CU "symmetric predecessor comparison and index transport"]
theorem powRightPredIso_symm_naturality_index
    (e : C ≌ C) {m n : ℤ} (h : m = n) :
    (powRightPredIso e m).symm ≪≫
        Functor.isoWhiskerRight (powIndexIso e h) e.inverse =
      powIndexIso e (congrArg (fun k : ℤ ↦ k - 1) h) ≪≫
        (powRightPredIso e n).symm := by
  subst n
  simp [powIndexIso]

/-- Addition comparison when the second exponent is nonnegative. -/
noncomputable def PowAux.powAddOfNatIso (e : C ≌ C) (m : ℤ) :
    (n : ℕ) →
      (e ^ (m + (n : ℤ))).functor ≅ (e ^ m).functor ⋙ (e ^ (n : ℤ)).functor
  | 0 =>
      powIndexIso e (Int.add_zero m) ≪≫
        (Functor.rightUnitor (e ^ m).functor).symm
  | n + 1 =>
      powIndexIso e (PowAux.addOfNatSucc m n) ≪≫
        (powRightSuccIso e (m + (n : ℤ))).symm ≪≫
        Functor.isoWhiskerRight (PowAux.powAddOfNatIso e m n) e.functor ≪≫
        Functor.associator (e ^ m).functor (e ^ (n : ℤ)).functor e.functor ≪≫
        Functor.isoWhiskerLeft (e ^ m).functor (powRightSuccIso e (n : ℤ)) ≪≫
        Functor.isoWhiskerLeft (e ^ m).functor
          (powIndexIso e (PowAux.ofNatSucc n))

/-- Addition comparison when the second exponent is negative. -/
noncomputable def PowAux.powAddNegSuccIso (e : C ≌ C) (m : ℤ) :
    (n : ℕ) →
      (e ^ (m + Int.negSucc n)).functor ≅
        (e ^ m).functor ⋙ (e ^ Int.negSucc n).functor
  | 0 =>
      powIndexIso e (PowAux.addNegOne m) ≪≫
        (powRightPredIso e m).symm
  | n + 1 =>
      powIndexIso e (PowAux.addNegSucc m n) ≪≫
        (powRightPredIso e (m + Int.negSucc n)).symm ≪≫
        Functor.isoWhiskerRight (PowAux.powAddNegSuccIso e m n) e.inverse ≪≫
        Functor.associator (e ^ m).functor (e ^ Int.negSucc n).functor e.inverse ≪≫
        Functor.isoWhiskerLeft (e ^ m).functor (powRightPredIso e (Int.negSucc n)) ≪≫
        Functor.isoWhiskerLeft (e ^ m).functor
          (powIndexIso e (PowAux.negSuccPred n))

set_option backward.isDefEq.respectTransparency false in
/-- Adding a nonnegative exponent to the zero power is the canonical zero-power left action. -/
@[stacks 01CU "nonnegative addition to the zero power"]
theorem PowAux.powAddOfNatIso_zero (e : C ≌ C) (n : ℕ) :
    PowAux.powAddOfNatIso e 0 n =
      powIndexIso e (Int.zero_add (n : ℤ)) ≪≫
        PowAux.powZeroLeftIso e (e ^ (n : ℤ)).functor := by
  induction n with
  | zero =>
      apply Iso.ext
      ext A
      simp [PowAux.powAddOfNatIso, PowAux.powZeroLeftIso, powIndexIso, powZeroIso]
      exact ((Equivalence.refl : C ≌ C).functor.map_id _).symm
  | succ n ih =>
      rw [PowAux.powAddOfNatIso, ih]
      simp only [Functor.isoWhiskerRight_trans, Iso.trans_assoc]
      rw [powRightSuccIso_symm_naturality_index_assoc e (Int.zero_add (n : ℤ))]
      rw [PowAux.powZeroLeftIso_comp_assoc]
      rw [PowAux.powZeroLeftIso_conj_assoc]
      rw [← PowAux.powZeroLeftIso_naturality e
        (powIndexIso e (PowAux.ofNatSucc n))]
      rw [powIndexIso_trans_assoc e (PowAux.addOfNatSucc 0 n)
        (congrArg (fun k : ℤ ↦ k + 1) (Int.zero_add (n : ℤ)))]
      rw [powIndexIso_trans_assoc e
        ((PowAux.addOfNatSucc 0 n).trans
          (congrArg (fun k : ℤ ↦ k + 1) (Int.zero_add (n : ℤ))))
        (PowAux.ofNatSucc n)]

set_option backward.isDefEq.respectTransparency false in
/-- Adding a negative exponent to the zero power is the canonical zero-power left action. -/
@[stacks 01CU "negative addition to the zero power"]
theorem PowAux.powAddNegSuccIso_zero (e : C ≌ C) (n : ℕ) :
    PowAux.powAddNegSuccIso e 0 n =
      powIndexIso e (Int.zero_add (Int.negSucc n)) ≪≫
        PowAux.powZeroLeftIso e (e ^ Int.negSucc n).functor := by
  induction n with
  | zero =>
      apply Iso.ext
      ext A
      simp [PowAux.powAddNegSuccIso, powRightPredIso, PowAux.powZeroLeftIso,
        powIndexIso, powZeroIso, powRightSuccIso, powRightSuccNatTrans]
      have hs : (powRightSuccApp e A (-1)).hom = e.counit.app A := rfl
      rw [hs]
      have htriangle :
          e.unitIso.hom.app (e.inverse.obj A) ≫
              e.inverse.map (e.counitIso.hom.app A) =
            e.inverse.map (𝟙 A) := by
        rw [e.unit_inverse_comp, e.inverse.map_id]
      exact htriangle
  | succ n ih =>
      rw [PowAux.powAddNegSuccIso, ih]
      simp only [Functor.isoWhiskerRight_trans, Iso.trans_assoc]
      rw [powRightPredIso_symm_naturality_index_assoc e
        (Int.zero_add (Int.negSucc n))]
      rw [PowAux.powZeroLeftIso_comp_assoc]
      rw [PowAux.powZeroLeftIso_conj_assoc]
      rw [← PowAux.powZeroLeftIso_naturality e
        (powIndexIso e (PowAux.negSuccPred n))]
      rw [powIndexIso_trans_assoc e (PowAux.addNegSucc 0 n)
        (congrArg (fun k : ℤ ↦ k - 1) (Int.zero_add (Int.negSucc n)))]
      rw [powIndexIso_trans_assoc e
        ((PowAux.addNegSucc 0 n).trans
          (congrArg (fun k : ℤ ↦ k - 1) (Int.zero_add (Int.negSucc n))))
        (PowAux.negSuccPred n)]

/-- Powers of an autoequivalence add under functor composition. -/
@[stacks 01CU "addition comparison for powers of an autoequivalence"]
noncomputable def powAddIso (e : C ≌ C) (m : ℤ) :
    (n : ℤ) → (e ^ (m + n)).functor ≅ (e ^ m).functor ⋙ (e ^ n).functor
  | .ofNat n => PowAux.powAddOfNatIso e m n
  | .negSucc n => PowAux.powAddNegSuccIso e m n

/-- Evaluating the addition comparison identifies a single orbit step of degree `m + n` with
successive orbit steps of degrees `m` and `n`. -/
@[stacks 01CU "objectwise addition for powers of an autoequivalence"]
noncomputable def powObjAddIso (e : C ≌ C) (A : C) (m n : ℤ) :
    (e ^ (m + n)).functor.obj A ≅
      (e ^ n).functor.obj ((e ^ m).functor.obj A) :=
  (powAddIso e m n).app A

/-- Associativity law for the composition comparison between powers of an autoequivalence. -/
theorem powAddIso_assoc_hom_app
    (e : C ≌ C) (m₁ m₂ m₃ : ℤ) (A : C) :
    (powAddIso e (m₁ + m₂) m₃).hom.app A ≫
        (e ^ m₃).functor.map ((powAddIso e m₁ m₂).hom.app A) =
      eqToHom (congrArg (fun n : ℤ ↦ (e ^ n).functor.obj A)
          (Int.add_assoc m₁ m₂ m₃)) ≫
        (powAddIso e m₁ (m₂ + m₃)).hom.app A ≫
        (powAddIso e m₂ m₃).hom.app ((e ^ m₁).functor.obj A) := sorry

set_option backward.isDefEq.respectTransparency false in
/-- Left-unit law for the composition comparison between powers of an autoequivalence. -/
theorem powAddIso_zero_add_hom_app
    (e : C ≌ C) (n : ℤ) (A : C) :
    (powAddIso e 0 n).hom.app A =
      eqToHom (congrArg (fun k : ℤ ↦ (e ^ k).functor.obj A) (Int.zero_add n)) ≫
        (e ^ n).functor.map ((powZeroIso e).inv.app A) := by
  rcases n with n | n
  · change (PowAux.powAddOfNatIso e 0 n).hom.app A = _
    rw [PowAux.powAddOfNatIso_zero]
    simp [PowAux.powZeroLeftIso, powIndexIso]
  · change (PowAux.powAddNegSuccIso e 0 n).hom.app A = _
    rw [PowAux.powAddNegSuccIso_zero]
    simp [PowAux.powZeroLeftIso, powIndexIso]
    exact Category.id_comp _

/-- Right-unit law for the composition comparison between powers of an autoequivalence. -/
theorem powAddIso_add_zero_hom_app
    (e : C ≌ C) (n : ℤ) (A : C) :
    (powAddIso e n 0).hom.app A =
      eqToHom (congrArg (fun k : ℤ ↦ (e ^ k).functor.obj A) (Int.add_zero n)) ≫
        (powZeroIso e).inv.app ((e ^ n).functor.obj A) := by
  simp [powAddIso, PowAux.powAddOfNatIso, powZeroIso, powIndexIso]
  rfl

/-- The coherent `ℤ`-indexed shift core generated by an autoequivalence. It is kept as explicit
data because the type `HasShift C ℤ` does not record which autoequivalence generated the shift. -/
@[stacks 01CU "shift core generated by an autoequivalence"]
noncomputable def powShiftCore (e : C ≌ C) : ShiftMkCore C ℤ where
  F n := (e ^ n).functor
  zero := powZeroIso e
  add := powAddIso e
  assoc_hom_app := powAddIso_assoc_hom_app e
  zero_add_hom_app := powAddIso_zero_add_hom_app e
  add_zero_hom_app := powAddIso_add_zero_hom_app e

/-- The `ℤ`-indexed shift generated by an autoequivalence, exposed as an ordinary definition so
that callers must choose explicitly when several autoequivalences are present. -/
@[reducible, stacks 01CU "shift generated by an autoequivalence"]
noncomputable def powHasShift (e : C ≌ C) : HasShift C ℤ :=
  hasShiftMk C ℤ (powShiftCore e)

end CategoryTheory.Equivalence


