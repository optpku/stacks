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
  map_add' := sorry
  map_smul' := sorry

/-- Lemma 22.4.2 (09JJ), left-module form: the degreewise direct-sum coproduct of a family of
left differential graded `A`-modules. -/
@[stacks 09JJ "degreewise coproducts of left differential graded modules"]
def obj : LeftDifferentialGradedModule.{u, max v w} A where
  X := degree M
  d := differential M
  smul := action M
  d_sq := sorry
  smul_one := sorry
  smul_mul := sorry
  comm_d := sorry

/-- The coproduct object has the degreewise direct sum as its carrier. -/
@[simp] theorem obj_X (n : ℤ) : (obj M).X n = degree M n := sorry

/-- The differential of the coproduct object is the coordinatewise differential. -/
@[simp] theorem obj_d (n : ℤ) : (obj M).d n = differential M n := sorry

/-- The action on the coproduct object is the coordinatewise action. -/
@[simp] theorem obj_smul (i p : ℤ) : (obj M).smul i p = action M i p := sorry

/-- The canonical linear injection into the degree-`n` carrier of the coproduct. -/
def injectionLinearMap (j : I) (n : ℤ) : (M j).X n →ₗ[R] degree M n :=
  DifferentialGradedModule.DirectSum.injectionWith
    (R := R) (X := fun k ↦ (M k).X n) j
    (decidableEqI := Classical.decEq I)

/-- The coproduct differential sends an injected homogeneous element to the injection of its
differential. -/
@[simp] theorem differential_injection_apply (j : I) (n : ℤ) (x : (M j).X n) :
    differential M n (injectionLinearMap M j n x) =
      injectionLinearMap M j (n + 1) ((M j).d n x) := sorry

/-- The coproduct left action sends an injected homogeneous element to the injection of its
coordinatewise action. -/
@[simp] theorem action_injection_apply (j : I) (i p : ℤ) (a : A.X i) (x : (M j).X p) :
    action M i p a (injectionLinearMap M j p x) =
      injectionLinearMap M j (i + p) ((M j).smul i p a x) := sorry

/-- The canonical inclusion of one left differential graded module into the coproduct. -/
def ι (j : I) : M j ⟶ obj M where
  hom n := injectionLinearMap M j n
  comm_d := sorry
  comm_smul := sorry

/-- The homogeneous component of a coproduct injection is the direct-sum injection. -/
@[simp] theorem ι_hom (j : I) (n : ℤ) : (ι M j).hom n = injectionLinearMap M j n := sorry

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
  comm_d := sorry
  comm_smul := sorry

/-- The homogeneous component of coproduct descent is direct-sum descent. -/
@[simp] theorem desc_hom {N : LeftDifferentialGradedModule.{u, max v w} A}
    (f : ∀ j, M j ⟶ N) (n : ℤ) : (desc M f).hom n = descLinearMap M f n := sorry

/-- A coproduct injection followed by descent recovers the corresponding morphism. -/
@[reassoc] theorem ι_desc {N : LeftDifferentialGradedModule.{u, max v w} A}
    (f : ∀ j, M j ⟶ N) (j : I) : ι M j ≫ desc M f = f j := sorry

/-- Morphisms out of the direct-sum coproduct are determined by all coproduct injections. -/
@[ext] theorem hom_ext {N : LeftDifferentialGradedModule.{u, max v w} A}
    (f g : obj M ⟶ N) (h : ∀ j, ι M j ≫ f = ι M j ≫ g) : f = g := sorry

/-- The cofan formed by the explicit direct-sum object and its canonical injections. -/
def cofan : Cofan M :=
  Cofan.mk (obj M) (ι M)

/-- The legs of the coproduct cofan are the canonical direct-sum injections. -/
@[simp] theorem cofan_inj (j : I) : (cofan M).inj j = ι M j := sorry

/-- The explicit descent map factors every cofan through the direct-sum cofan. -/
@[reassoc] theorem cofan_fac (S : Cofan M) (j : I) :
    (cofan M).inj j ≫ desc M S.inj = S.inj j := sorry

/-- The explicit descent map is the unique factorization of a cofan. -/
theorem cofan_uniq (S : Cofan M) (f : (cofan M).pt ⟶ S.pt)
    (h : ∀ j, (cofan M).inj j ≫ f = S.inj j) :
    f = desc M S.inj := sorry

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
    Sigma.ι M j ≫ (iso M).hom = ι M j := sorry

/-- An explicit direct-sum injection followed by the inverse comparison is the corresponding
categorical coproduct injection. -/
@[reassoc (attr := simp)] theorem ι_iso_inv (j : I) :
    ι M j ≫ (iso M).inv = Sigma.ι M j := sorry

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
  map_add' := sorry
  map_smul' := sorry

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
      injectionLinearMap M j (n + 1) ((M j).d n x) := sorry

/-- The coproduct right action sends an injected homogeneous element to the injection of its
coordinatewise action. -/
@[simp] theorem action_injection_apply (j : I) (p i : ℤ) (x : (M j).X p) (a : A.X i) :
    action M p i (injectionLinearMap M j p x) a =
      injectionLinearMap M j (p + i) ((M j).smul p i x a) := sorry

/-- Lemma 22.4.2 (09JJ): the degreewise direct-sum coproduct of a family of right differential
graded `A`-modules. -/
@[stacks 09JJ "degreewise coproducts of right differential graded modules"]
def obj : DifferentialGradedModule.{u, max v w} A where
  X := degree M
  d := differential M
  smul := action M
  d_sq := sorry
  smul_one := sorry
  smul_mul := sorry
  comm_d := sorry

/-- The coproduct object has the degreewise direct sum as its carrier. -/
@[simp] theorem obj_X (n : ℤ) : (obj M).X n = degree M n := sorry

/-- The differential of the coproduct object is the coordinatewise differential. -/
@[simp] theorem obj_d (n : ℤ) : (obj M).d n = differential M n := sorry

/-- The right action on the coproduct object is the coordinatewise action. -/
@[simp] theorem obj_smul (p i : ℤ) : (obj M).smul p i = action M p i := sorry

/-- The canonical inclusion of one right differential graded module into the coproduct. -/
def ι (j : I) : M j ⟶ obj M where
  hom n := injectionLinearMap M j n
  comm_d := sorry
  comm_smul := sorry

/-- The homogeneous component of a coproduct injection is the direct-sum injection. -/
@[simp] theorem ι_hom (j : I) (n : ℤ) : (ι M j).hom n = injectionLinearMap M j n := sorry

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
  comm_d := sorry
  comm_smul := sorry

/-- The homogeneous component of coproduct descent is direct-sum descent. -/
@[simp] theorem desc_hom {N : DifferentialGradedModule.{u, max v w} A}
    (f : ∀ j, M j ⟶ N) (n : ℤ) : (desc M f).hom n = descLinearMap M f n := sorry

/-- A coproduct injection followed by descent recovers the corresponding morphism. -/
@[reassoc] theorem ι_desc {N : DifferentialGradedModule.{u, max v w} A}
    (f : ∀ j, M j ⟶ N) (j : I) : ι M j ≫ desc M f = f j := sorry

/-- Morphisms out of the direct-sum coproduct are determined by all coproduct injections. -/
@[ext] theorem hom_ext {N : DifferentialGradedModule.{u, max v w} A}
    (f g : obj M ⟶ N) (h : ∀ j, ι M j ≫ f = ι M j ≫ g) : f = g := sorry

/-- The cofan formed by the explicit direct-sum object and its canonical injections. -/
def cofan : Cofan M :=
  Cofan.mk (obj M) (ι M)

/-- The legs of the coproduct cofan are the canonical direct-sum injections. -/
@[simp] theorem cofan_inj (j : I) : (cofan M).inj j = ι M j := sorry

/-- The explicit descent map factors every cofan through the direct-sum cofan. -/
@[reassoc] theorem cofan_fac (S : Cofan M) (j : I) :
    (cofan M).inj j ≫ desc M S.inj = S.inj j := sorry

/-- The explicit descent map is the unique factorization of a cofan. -/
theorem cofan_uniq (S : Cofan M) (f : (cofan M).pt ⟶ S.pt)
    (h : ∀ j, (cofan M).inj j ≫ f = S.inj j) :
    f = desc M S.inj := sorry

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
    Sigma.ι M j ≫ (iso M).hom = ι M j := sorry

/-- An explicit direct-sum injection followed by the inverse comparison is the corresponding
categorical coproduct injection. -/
@[reassoc (attr := simp)] theorem ι_iso_inv (j : I) :
    ι M j ≫ (iso M).inv = Sigma.ι M j := sorry

end Coproduct

end DifferentialGradedModule
