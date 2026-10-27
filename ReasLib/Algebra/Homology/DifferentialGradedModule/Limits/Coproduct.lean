/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Left
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Coproducts of Differential Graded Modules

This file constructs coproducts in the actual categories of left and right differential graded
modules.  The carrier in each degree is a direct sum, and the differential and action are induced
coordinatewise.  The injections and descent map expose the concrete direct-sum presentation;
the categorical coproduct instances are obtained only after this data and its universal property
have been assembled for each handedness.
-/

@[expose] public section

noncomputable section

universe u v w x z

open CategoryTheory CategoryTheory.Limits

namespace DifferentialGradedModule.DirectSum

/-- A direct-sum injection with the decidable equality on the index supplied explicitly. -/
def injectionWith {R : Type u} [CommRing R] {I : Type v}
    {X : I → Type w} [∀ j, AddCommMonoid (X j)] [∀ j, Module R (X j)]
    (j : I) [decidableEqI : DecidableEq I] : X j →ₗ[R] DirectSum I X :=
  DirectSum.lof R I X j

/-- Direct-sum descent with the decidable equality on the index supplied explicitly. -/
def descWith {R : Type u} [CommRing R] {I : Type v}
    {X : I → Type w} [∀ j, AddCommMonoid (X j)] [∀ j, Module R (X j)]
    {N : Type z} [AddCommMonoid N] [Module R N] (f : ∀ j, X j →ₗ[R] N)
    [decidableEqI : DecidableEq I] : DirectSum I X →ₗ[R] N :=
  DirectSum.toModule R I N f

/-- Transport between equal degrees commutes with taking a direct-sum coordinate. -/
theorem cast_apply {I : Type v} {X : ℤ → I → Type w} [∀ n j, AddCommMonoid (X n j)]
    {p q : ℤ} (h : p = q) (e : DirectSum I (X p) = DirectSum I (X q))
    (x : DirectSum I (X p)) (j : I) (ej : X p j = X q j) :
    (cast e x) j = cast ej (x j) := by
  subst q
  rfl

end DifferentialGradedModule.DirectSum

namespace LeftDifferentialGradedModule

variable {R : Type u} [CommRing R] {A : CochainDGAlgebra.{u, x} R}

namespace Coproduct

variable {I : Type v} (M : I → LeftDifferentialGradedModule.{u, max v w} A)

/-- The degree-`n` carrier of a coproduct of left differential graded modules. -/
abbrev degree (n : ℤ) : ModuleCat.{max v w} R :=
  ModuleCat.of R (DirectSum I (fun j ↦ (M j).X n))

/-- The coordinatewise differential on the degreewise direct sum. -/
def differential (n : ℤ) : degree M n →ₗ[R] degree M (n + 1) :=
  DirectSum.lmap (fun j ↦ (M j).d n)

/-- The coordinatewise left action on the degreewise direct sum. -/
def action (i p : ℤ) : A.X i →ₗ[R] degree M p →ₗ[R] degree M (i + p) where
  toFun a := DirectSum.lmap (fun j ↦ (M j).smul i p a)
  map_add' := by
    intro a b
    apply LinearMap.ext
    intro x
    apply DFinsupp.ext
    intro j
    change (M j).smul i p (a + b) (x j) =
      (M j).smul i p a (x j) + (M j).smul i p b (x j)
    simp
  map_smul' := by
    intro r a
    apply LinearMap.ext
    intro x
    apply DFinsupp.ext
    intro j
    change (M j).smul i p (r • a) (x j) = r • (M j).smul i p a (x j)
    simp

/-- Lemma 22.4.2 (09JJ), left-module form: the degreewise direct-sum coproduct of a family of
left differential graded `A`-modules. -/
@[stacks 09JJ "degreewise coproducts of left differential graded modules"]
def obj : LeftDifferentialGradedModule.{u, max v w} A where
  X := degree M
  d := differential M
  smul := action M
  d_sq := by
    intro n x
    apply DFinsupp.ext
    intro j
    exact (M j).d_sq n (x j)
  smul_one := by
    intro r p x
    apply DFinsupp.ext
    intro j
    rw [DifferentialGradedModule.DirectSum.cast_apply (X := fun n j ↦ (M j).X n)
      (zero_add p).symm _ _ j (zeroActionTarget p)]
    exact (M j).smul_one r p (x j)
  smul_mul := by
    intro i j p a b x
    apply DFinsupp.ext
    intro k
    rw [DifferentialGradedModule.DirectSum.cast_apply (X := fun n j ↦ (M j).X n)
      (add_assoc i j p).symm _ _ k (mulActionTarget p i j)]
    exact (M k).smul_mul i j p a b (x k)
  comm_d := by
    intro i p a x
    apply DFinsupp.ext
    intro j
    change (M j).d (i + p) ((M j).smul i p a (x j)) =
      (cast (dLeftActionTarget (M := degree M) p i)
          (action M (i + 1) p (A.d i a) x)) j +
        (i.negOnePow : R) •
          (cast (dRightActionTarget (M := degree M) p i)
            (action M i (p + 1) a (differential M p x))) j
    rw [DifferentialGradedModule.DirectSum.cast_apply (X := fun n j ↦ (M j).X n)
      (by omega : (i + 1) + p = i + p + 1) _ _ j (dLeftActionTarget p i),
      DifferentialGradedModule.DirectSum.cast_apply (X := fun n j ↦ (M j).X n)
      (add_assoc i p 1).symm _ _ j (dRightActionTarget p i)]
    exact (M j).comm_d i p a (x j)

/-- The coproduct object has the degreewise direct sum as its carrier. -/
@[simp] theorem obj_X (n : ℤ) : (obj M).X n = degree M n := rfl

/-- The differential of the coproduct object is the coordinatewise differential. -/
@[simp] theorem obj_d (n : ℤ) : (obj M).d n = differential M n := rfl

/-- The action on the coproduct object is the coordinatewise action. -/
@[simp] theorem obj_smul (i p : ℤ) : (obj M).smul i p = action M i p := rfl

/-- The canonical linear injection into the degree-`n` carrier of the coproduct. -/
def injectionLinearMap (j : I) (n : ℤ) : (M j).X n →ₗ[R] degree M n :=
  DifferentialGradedModule.DirectSum.injectionWith
    (R := R) (X := fun k ↦ (M k).X n) j
    (decidableEqI := Classical.decEq I)

/-- The coproduct differential sends an injected homogeneous element to the injection of its
differential. -/
@[simp] theorem differential_injection_apply (j : I) (n : ℤ) (x : (M j).X n) :
    differential M n (injectionLinearMap M j n x) =
      injectionLinearMap M j (n + 1) ((M j).d n x) := by
  classical
  simp only [differential, injectionLinearMap,
    DifferentialGradedModule.DirectSum.injectionWith, DirectSum.lmap_lof]

/-- The coproduct left action sends an injected homogeneous element to the injection of its
coordinatewise action. -/
@[simp] theorem action_injection_apply (j : I) (i p : ℤ) (a : A.X i) (x : (M j).X p) :
    action M i p a (injectionLinearMap M j p x) =
      injectionLinearMap M j (i + p) ((M j).smul i p a x) := by
  classical
  exact DirectSum.lmap_lof _ _ _

/-- The canonical inclusion of one left differential graded module into the coproduct. -/
def ι (j : I) : M j ⟶ obj M where
  hom n := injectionLinearMap M j n
  comm_d := by
    intro n x
    exact (differential_injection_apply M j n x).symm
  comm_smul := by
    intro i p a x
    exact (action_injection_apply M j i p a x).symm

/-- The homogeneous component of a coproduct injection is the direct-sum injection. -/
@[simp] theorem ι_hom (j : I) (n : ℤ) : (ι M j).hom n = injectionLinearMap M j n := rfl

/-- The degree-`n` linear descent from the direct sum for a family of compatible targets. -/
def descLinearMap {N : LeftDifferentialGradedModule.{u, max v w} A}
    (f : ∀ j, M j ⟶ N) (n : ℤ) : degree M n →ₗ[R] N.X n :=
  DifferentialGradedModule.DirectSum.descWith
    (R := R) (X := fun j ↦ (M j).X n) (N := N.X n)
    (fun j ↦ (f j).hom n) (decidableEqI := Classical.decEq I)

/-- The morphism out of the coproduct induced by a family of left DG-module morphisms. -/
def desc {N : LeftDifferentialGradedModule.{u, max v w} A}
    (f : ∀ j, M j ⟶ N) : obj M ⟶ N where
  hom n := descLinearMap M f n
  comm_d := by
    intro n x
    classical
    have h : (descLinearMap M f (n + 1)).comp (differential M n) =
        (N.d n).comp (descLinearMap M f n) := by
      apply DirectSum.linearMap_ext
      intro j
      apply LinearMap.ext
      intro y
      change descLinearMap M f (n + 1)
          (differential M n (injectionLinearMap M j n y)) =
        N.d n (descLinearMap M f n (injectionLinearMap M j n y))
      rw [differential_injection_apply]
      simpa only [descLinearMap, injectionLinearMap,
        DifferentialGradedModule.DirectSum.injectionWith,
        DifferentialGradedModule.DirectSum.descWith, DirectSum.toModule_lof] using
        (f j).comm_d n y
    exact LinearMap.congr_fun h x
  comm_smul := by
    intro i p a x
    classical
    have h : (descLinearMap M f (i + p)).comp (action M i p a) =
        (N.smul i p a).comp (descLinearMap M f p) := by
      apply DirectSum.linearMap_ext
      intro j
      apply LinearMap.ext
      intro y
      change descLinearMap M f (i + p)
          (action M i p a (injectionLinearMap M j p y)) =
        N.smul i p a (descLinearMap M f p (injectionLinearMap M j p y))
      rw [action_injection_apply]
      simpa only [descLinearMap, injectionLinearMap,
        DifferentialGradedModule.DirectSum.injectionWith,
        DifferentialGradedModule.DirectSum.descWith, DirectSum.toModule_lof] using
        (f j).comm_smul i p a y
    exact LinearMap.congr_fun h x

/-- The homogeneous component of coproduct descent is direct-sum descent. -/
@[simp] theorem desc_hom {N : LeftDifferentialGradedModule.{u, max v w} A}
    (f : ∀ j, M j ⟶ N) (n : ℤ) : (desc M f).hom n = descLinearMap M f n := rfl

/-- A coproduct injection followed by descent recovers the corresponding morphism. -/
@[reassoc] theorem ι_desc {N : LeftDifferentialGradedModule.{u, max v w} A}
    (f : ∀ j, M j ⟶ N) (j : I) : ι M j ≫ desc M f = f j := by
  classical
  apply LeftDifferentialGradedModule.hom_ext
  intro n x
  change descLinearMap M f n (injectionLinearMap M j n x) = (f j).hom n x
  simp only [descLinearMap, injectionLinearMap,
    DifferentialGradedModule.DirectSum.injectionWith,
    DifferentialGradedModule.DirectSum.descWith, DirectSum.toModule_lof]

/-- Morphisms out of the direct-sum coproduct are determined by all coproduct injections. -/
@[ext] theorem hom_ext {N : LeftDifferentialGradedModule.{u, max v w} A}
    (f g : obj M ⟶ N) (h : ∀ j, ι M j ≫ f = ι M j ≫ g) : f = g := by
  classical
  apply LeftDifferentialGradedModule.hom_ext
  intro n x
  have hn : f.hom n = g.hom n := by
    apply DirectSum.linearMap_ext
    intro j
    apply LinearMap.ext
    intro y
    exact congrArg (fun t ↦ t.hom n y) (h j)
  exact LinearMap.congr_fun hn x

/-- The cofan formed by the explicit direct-sum object and its canonical injections. -/
def cofan : Cofan M :=
  Cofan.mk (obj M) (ι M)

/-- The legs of the coproduct cofan are the canonical direct-sum injections. -/
@[simp] theorem cofan_inj (j : I) : (cofan M).inj j = ι M j := rfl

/-- The explicit descent map factors every cofan through the direct-sum cofan. -/
@[reassoc] theorem cofan_fac (S : Cofan M) (j : I) :
    (cofan M).inj j ≫ desc M S.inj = S.inj j := by
  exact ι_desc M S.inj j

/-- The explicit descent map is the unique factorization of a cofan. -/
theorem cofan_uniq (S : Cofan M) (f : (cofan M).pt ⟶ S.pt)
    (h : ∀ j, (cofan M).inj j ≫ f = S.inj j) :
    f = desc M S.inj := by
  apply hom_ext M
  intro j
  exact (h j).trans (ι_desc M S.inj j).symm

/-- The explicit direct-sum cofan is a colimit cofan. -/
def isColimit : IsColimit (cofan M) :=
  Cofan.IsColimit.mk (cofan M)
    (fun S ↦ desc M S.inj)
    (fun S j ↦ cofan_fac M S j)
    (fun S f h ↦ cofan_uniq M S f h)

end Coproduct

/-- Lemma 22.4.2 (09JJ), left-module form: left differential graded modules over a fixed algebra
have arbitrary degreewise coproducts. -/
@[stacks 09JJ "arbitrary coproducts of left differential graded modules"]
instance instHasCoproducts (A : CochainDGAlgebra.{u, x} R) :
    HasCoproducts.{v} (LeftDifferentialGradedModule.{u, max v w} A) :=
  hasCoproducts_of_colimit_cofans
    (fun M ↦ Coproduct.cofan M)
    (fun M ↦ Coproduct.isColimit M)

namespace Coproduct

variable {I : Type v} (M : I → LeftDifferentialGradedModule.{u, max v w} A)

/-- The categorical coproduct is canonically isomorphic to the explicit degreewise direct sum. -/
noncomputable def iso : ∐ M ≅ obj M :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (isColimit M)

/-- A categorical coproduct injection followed by the concrete comparison is the explicit
direct-sum injection. -/
@[reassoc (attr := simp)] theorem sigma_ι_iso_hom (j : I) :
    Sigma.ι M j ≫ (iso M).hom = ι M j := by
  exact (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom (isColimit M) ⟨j⟩

/-- An explicit direct-sum injection followed by the inverse comparison is the corresponding
categorical coproduct injection. -/
@[reassoc (attr := simp)] theorem ι_iso_inv (j : I) :
    ι M j ≫ (iso M).inv = Sigma.ι M j := by
  exact (colimit.isColimit _).comp_coconePointUniqueUpToIso_inv (isColimit M) ⟨j⟩

end Coproduct

end LeftDifferentialGradedModule

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : CochainDGAlgebra.{u, x} R}

namespace Coproduct

variable {I : Type v} (M : I → DifferentialGradedModule.{u, max v w} A)

/-- The degree-`n` carrier of a coproduct of right differential graded modules. -/
abbrev degree (n : ℤ) : ModuleCat.{max v w} R :=
  ModuleCat.of R (DirectSum I (fun j ↦ (M j).X n))

/-- The coordinatewise differential on the degreewise direct sum. -/
def differential (n : ℤ) : degree M n →ₗ[R] degree M (n + 1) :=
  DirectSum.lmap (fun j ↦ (M j).d n)

/-- The canonical linear injection into the degree-`n` carrier of the coproduct. -/
def injectionLinearMap (j : I) (n : ℤ) : (M j).X n →ₗ[R] degree M n :=
  DifferentialGradedModule.DirectSum.injectionWith
    (R := R) (X := fun k ↦ (M k).X n) j
    (decidableEqI := Classical.decEq I)

/-- The contribution of one summand to the coordinatewise right action. -/
def actionSummand (p i : ℤ) (j : I) :
    (M j).X p →ₗ[R] A.X i →ₗ[R] degree M (p + i) where
  toFun x := (injectionLinearMap M j (p + i)).comp ((M j).smul p i x)
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro a
    change injectionLinearMap M j (p + i) ((M j).smul p i (x + y) a) =
      injectionLinearMap M j (p + i) ((M j).smul p i x a) +
        injectionLinearMap M j (p + i) ((M j).smul p i y a)
    simp
  map_smul' := by
    intro r x
    apply LinearMap.ext
    intro a
    change injectionLinearMap M j (p + i) ((M j).smul p i (r • x) a) =
      r • injectionLinearMap M j (p + i) ((M j).smul p i x a)
    simp

/-- The coordinatewise right action on the degreewise direct sum. -/
def action (p i : ℤ) : degree M p →ₗ[R] A.X i →ₗ[R] degree M (p + i) :=
  DifferentialGradedModule.DirectSum.descWith
    (R := R) (X := fun j ↦ (M j).X p)
    (N := A.X i →ₗ[R] degree M (p + i)) (fun j ↦ actionSummand M p i j)
    (decidableEqI := Classical.decEq I)

/-- The coproduct differential sends an injected homogeneous element to the injection of its
differential. -/
@[simp] theorem differential_injection_apply (j : I) (n : ℤ) (x : (M j).X n) :
    differential M n (injectionLinearMap M j n x) =
      injectionLinearMap M j (n + 1) ((M j).d n x) := by
  classical
  simp only [differential, injectionLinearMap,
    DifferentialGradedModule.DirectSum.injectionWith, DirectSum.lmap_lof]

/-- The coproduct right action sends an injected homogeneous element to the injection of its
coordinatewise action. -/
@[simp] theorem action_injection_apply (j : I) (p i : ℤ) (x : (M j).X p) (a : A.X i) :
    action M p i (injectionLinearMap M j p x) a =
      injectionLinearMap M j (p + i) ((M j).smul p i x a) := by
  classical
  simp only [action, injectionLinearMap,
    DifferentialGradedModule.DirectSum.injectionWith,
    DifferentialGradedModule.DirectSum.descWith, DirectSum.toModule_lof,
    actionSummand]
  rfl

/-- The right action is evaluated coordinatewise. -/
@[simp] theorem action_apply (p i : ℤ) (x : degree M p) (a : A.X i) (j : I) :
    action M p i x a j = (M j).smul p i (x j) a := by
  classical
  have h : (action M p i).flip a =
      DirectSum.lmap (fun k ↦ ((M k).smul p i).flip a) := by
    apply DirectSum.linearMap_ext
    intro k
    apply LinearMap.ext
    intro y
    simpa only [injectionLinearMap, DifferentialGradedModule.DirectSum.injectionWith,
      LinearMap.comp_apply, LinearMap.flip_apply, DirectSum.lmap_lof] using
      action_injection_apply M k p i y a
  exact congrArg (fun y : degree M (p + i) ↦ y j) (LinearMap.congr_fun h x)

/-- Lemma 22.4.2 (09JJ): the degreewise direct-sum coproduct of a family of right differential
graded `A`-modules. -/
@[stacks 09JJ "degreewise coproducts of right differential graded modules"]
def obj : DifferentialGradedModule.{u, max v w} A where
  X := degree M
  d := differential M
  smul := action M
  d_sq := by
    intro n x
    apply DFinsupp.ext
    intro j
    exact (M j).d_sq n (x j)
  smul_one := by
    intro r p x
    apply DFinsupp.ext
    intro j
    rw [action_apply,
      DifferentialGradedModule.DirectSum.cast_apply (X := fun n j ↦ (M j).X n)
        (add_zero p).symm _ _ j (zeroActionTarget p)]
    exact (M j).smul_one r p (x j)
  smul_mul := by
    intro p i j x a b
    apply DFinsupp.ext
    intro k
    rw [action_apply,
      DifferentialGradedModule.DirectSum.cast_apply (X := fun n j ↦ (M j).X n)
        (add_assoc p i j) _ _ k (mulActionTarget p i j), action_apply, action_apply]
    exact (M k).smul_mul p i j (x k) a b
  comm_d := by
    intro p i x a
    apply DFinsupp.ext
    intro j
    change (M j).d (p + i) (action M p i x a j) =
      (cast (dLeftActionTarget (M := degree M) p i)
          (action M (p + 1) i (differential M p x) a)) j +
        (p.negOnePow : R) •
          (cast (dRightActionTarget (M := degree M) p i)
            (action M p (i + 1) x (A.d i a))) j
    rw [DifferentialGradedModule.DirectSum.cast_apply (X := fun n j ↦ (M j).X n)
      (by omega : (p + 1) + i = p + i + 1) _ _ j (dLeftActionTarget p i),
      DifferentialGradedModule.DirectSum.cast_apply (X := fun n j ↦ (M j).X n)
      (add_assoc p i 1).symm _ _ j (dRightActionTarget p i)]
    change (M j).d (p + i) (action M p i x a j) =
      cast (dLeftActionTarget p i) (action M (p + 1) i (differential M p x) a j) +
        (p.negOnePow : R) •
          cast (dRightActionTarget p i) (action M p (i + 1) x (A.d i a) j)
    rw [action_apply, action_apply, action_apply]
    exact (M j).comm_d p i (x j) a

/-- The coproduct object has the degreewise direct sum as its carrier. -/
@[simp] theorem obj_X (n : ℤ) : (obj M).X n = degree M n := rfl

/-- The differential of the coproduct object is the coordinatewise differential. -/
@[simp] theorem obj_d (n : ℤ) : (obj M).d n = differential M n := rfl

/-- The right action on the coproduct object is the coordinatewise action. -/
@[simp] theorem obj_smul (p i : ℤ) : (obj M).smul p i = action M p i := rfl

/-- The canonical inclusion of one right differential graded module into the coproduct. -/
def ι (j : I) : M j ⟶ obj M where
  hom n := injectionLinearMap M j n
  comm_d := by
    intro n x
    exact (differential_injection_apply M j n x).symm
  comm_smul := by
    intro p i x a
    exact (action_injection_apply M j p i x a).symm

/-- The homogeneous component of a coproduct injection is the direct-sum injection. -/
@[simp] theorem ι_hom (j : I) (n : ℤ) : (ι M j).hom n = injectionLinearMap M j n := rfl

/-- The degree-`n` linear descent from the direct sum for a family of compatible targets. -/
def descLinearMap {N : DifferentialGradedModule.{u, max v w} A}
    (f : ∀ j, M j ⟶ N) (n : ℤ) : degree M n →ₗ[R] N.X n :=
  DifferentialGradedModule.DirectSum.descWith
    (R := R) (X := fun j ↦ (M j).X n) (N := N.X n)
    (fun j ↦ (f j).hom n) (decidableEqI := Classical.decEq I)

/-- The morphism out of the coproduct induced by a family of right DG-module morphisms. -/
def desc {N : DifferentialGradedModule.{u, max v w} A}
    (f : ∀ j, M j ⟶ N) : obj M ⟶ N where
  hom n := descLinearMap M f n
  comm_d := by
    intro n x
    classical
    have h : (descLinearMap M f (n + 1)).comp (differential M n) =
        (N.d n).comp (descLinearMap M f n) := by
      apply DirectSum.linearMap_ext
      intro j
      apply LinearMap.ext
      intro y
      change descLinearMap M f (n + 1)
          (differential M n (injectionLinearMap M j n y)) =
        N.d n (descLinearMap M f n (injectionLinearMap M j n y))
      rw [differential_injection_apply]
      simpa only [descLinearMap, injectionLinearMap,
        DifferentialGradedModule.DirectSum.injectionWith,
        DifferentialGradedModule.DirectSum.descWith, DirectSum.toModule_lof] using
        (f j).comm_d n y
    exact LinearMap.congr_fun h x
  comm_smul := by
    intro p i x a
    classical
    have h : (descLinearMap M f (p + i)).comp ((action M p i).flip a) =
        ((N.smul p i).flip a).comp (descLinearMap M f p) := by
      apply DirectSum.linearMap_ext
      intro j
      apply LinearMap.ext
      intro y
      change descLinearMap M f (p + i)
          (action M p i (injectionLinearMap M j p y) a) =
        N.smul p i (descLinearMap M f p (injectionLinearMap M j p y)) a
      rw [action_injection_apply]
      simpa only [descLinearMap, injectionLinearMap,
        DifferentialGradedModule.DirectSum.injectionWith,
        DifferentialGradedModule.DirectSum.descWith, DirectSum.toModule_lof] using
        (f j).comm_smul p i y a
    exact LinearMap.congr_fun h x

/-- The homogeneous component of coproduct descent is direct-sum descent. -/
@[simp] theorem desc_hom {N : DifferentialGradedModule.{u, max v w} A}
    (f : ∀ j, M j ⟶ N) (n : ℤ) : (desc M f).hom n = descLinearMap M f n := rfl

/-- A coproduct injection followed by descent recovers the corresponding morphism. -/
@[reassoc] theorem ι_desc {N : DifferentialGradedModule.{u, max v w} A}
    (f : ∀ j, M j ⟶ N) (j : I) : ι M j ≫ desc M f = f j := by
  classical
  apply DifferentialGradedModule.hom_ext
  intro n x
  change descLinearMap M f n (injectionLinearMap M j n x) = (f j).hom n x
  simp only [descLinearMap, injectionLinearMap,
    DifferentialGradedModule.DirectSum.injectionWith,
    DifferentialGradedModule.DirectSum.descWith, DirectSum.toModule_lof]

/-- Morphisms out of the direct-sum coproduct are determined by all coproduct injections. -/
@[ext] theorem hom_ext {N : DifferentialGradedModule.{u, max v w} A}
    (f g : obj M ⟶ N) (h : ∀ j, ι M j ≫ f = ι M j ≫ g) : f = g := by
  classical
  apply DifferentialGradedModule.hom_ext
  intro n x
  have hn : f.hom n = g.hom n := by
    apply DirectSum.linearMap_ext
    intro j
    apply LinearMap.ext
    intro y
    exact congrArg (fun t ↦ t.hom n y) (h j)
  exact LinearMap.congr_fun hn x

/-- The cofan formed by the explicit direct-sum object and its canonical injections. -/
def cofan : Cofan M :=
  Cofan.mk (obj M) (ι M)

/-- The legs of the coproduct cofan are the canonical direct-sum injections. -/
@[simp] theorem cofan_inj (j : I) : (cofan M).inj j = ι M j := rfl

/-- The explicit descent map factors every cofan through the direct-sum cofan. -/
@[reassoc] theorem cofan_fac (S : Cofan M) (j : I) :
    (cofan M).inj j ≫ desc M S.inj = S.inj j := by
  exact ι_desc M S.inj j

/-- The explicit descent map is the unique factorization of a cofan. -/
theorem cofan_uniq (S : Cofan M) (f : (cofan M).pt ⟶ S.pt)
    (h : ∀ j, (cofan M).inj j ≫ f = S.inj j) :
    f = desc M S.inj := by
  apply hom_ext M
  intro j
  exact (h j).trans (ι_desc M S.inj j).symm

/-- The explicit direct-sum cofan is a colimit cofan. -/
def isColimit : IsColimit (cofan M) :=
  Cofan.IsColimit.mk (cofan M)
    (fun S ↦ desc M S.inj)
    (fun S j ↦ cofan_fac M S j)
    (fun S f h ↦ cofan_uniq M S f h)

end Coproduct

/-- Lemma 22.4.2 (09JJ): right differential graded modules over a fixed algebra have arbitrary
degreewise coproducts. -/
@[stacks 09JJ "arbitrary coproducts of right differential graded modules"]
instance instHasCoproducts (A : CochainDGAlgebra.{u, x} R) :
    HasCoproducts.{v} (DifferentialGradedModule.{u, max v w} A) :=
  hasCoproducts_of_colimit_cofans
    (fun M ↦ Coproduct.cofan M)
    (fun M ↦ Coproduct.isColimit M)

namespace Coproduct

variable {I : Type v} (M : I → DifferentialGradedModule.{u, max v w} A)

/-- The categorical coproduct is canonically isomorphic to the explicit degreewise direct sum. -/
noncomputable def iso : ∐ M ≅ obj M :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (isColimit M)

/-- A categorical coproduct injection followed by the concrete comparison is the explicit
direct-sum injection. -/
@[reassoc (attr := simp)] theorem sigma_ι_iso_hom (j : I) :
    Sigma.ι M j ≫ (iso M).hom = ι M j := by
  exact (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom (isColimit M) ⟨j⟩

/-- An explicit direct-sum injection followed by the inverse comparison is the corresponding
categorical coproduct injection. -/
@[reassoc (attr := simp)] theorem ι_iso_inv (j : I) :
    ι M j ≫ (iso M).inv = Sigma.ι M j := by
  exact (colimit.isColimit _).comp_coconePointUniqueUpToIso_inv (isColimit M) ⟨j⟩

end Coproduct

end DifferentialGradedModule
