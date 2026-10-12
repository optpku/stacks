/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom
public import Mathlib.Algebra.Category.ModuleCat.Ulift

/-!
# Universe Lifts of Cochain Differential Graded Algebras

This file owns the carrier-only universe lift of a cochain DGA.  The multiplication and unit are
transported through `ULift`, while the coefficient ring and all graded indices remain unchanged.
-/

@[expose] public section

noncomputable section

universe u v w z l

open CategoryTheory ComplexShape HomologicalComplex

namespace CochainDGAlgebra

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}

/-- Lift a linear map through `ULift` on its source and target. -/
@[stacks 061V "universe lift of a graded linear map"]
def uliftLinear {X : ModuleCat.{v} R} {Y : ModuleCat.{w} R}
    (f : X →ₗ[R] Y) : ULift.{l} X →ₗ[R] ULift.{l} Y :=
  (ULift.moduleEquiv (R := R) (M := X)).symm.arrowCongr
    (ULift.moduleEquiv (R := R) (M := Y)).symm f

/-- A lifted linear map evaluates by lowering and raising. -/
@[simp, stacks 061V "evaluation of a lifted linear map"]
theorem uliftLinear_apply {X : ModuleCat.{v} R} {Y : ModuleCat.{w} R}
    (f : X →ₗ[R] Y) (x : ULift.{l} X) :
    uliftLinear.{u, v, w, l} f x = ULift.up (f x.down) := sorry

/-- Lift a curried homogeneous multiplication map through `ULift`. -/
@[stacks 061V "universe lift of homogeneous multiplication"]
def uliftMul {X : ModuleCat.{v} R} {Y : ModuleCat.{w} R} {Z : ModuleCat.{z} R}
    (f : X →ₗ[R] Y →ₗ[R] Z) :
    ULift.{l} X →ₗ[R] ULift.{l} Y →ₗ[R] ULift.{l} Z :=
  (ULift.moduleEquiv (R := R) (M := X)).symm.arrowCongr
    ((ULift.moduleEquiv (R := R) (M := Y)).symm.arrowCongr
      (ULift.moduleEquiv (R := R) (M := Z)).symm) f

/-- A lifted curried multiplication evaluates by lowering both inputs and raising the output. -/
@[simp, stacks 061V "evaluation of a lifted curried map"]
theorem uliftMul_apply {X : ModuleCat.{v} R} {Y : ModuleCat.{w} R} {Z : ModuleCat.{z} R}
    (f : X →ₗ[R] Y →ₗ[R] Z) (x : ULift.{l} X) (y : ULift.{l} Y) :
    uliftMul.{u, v, w, z, l} f x y = ULift.up (f x.down y.down) := sorry

/-- Carrier-only universe lift of a cochain differential graded algebra. -/
@[stacks 061V "universe lift of a cochain differential graded algebra"]
def ulift (A : CochainDGAlgebra.{u, v} R) :
    CochainDGAlgebra.{u, max v l} R where
  toCochainComplex :=
    ((ModuleCat.uliftFunctor.{l} R).mapHomologicalComplex (up ℤ)).obj A.toCochainComplex
  mul n m := uliftMul (A.mul n m)
  one := ULift.up A.one
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry
  leibniz := sorry

/-- A DGA homomorphism induces a homomorphism between its universe lifts. -/
@[stacks 061X "universe lift of a cochain DGA homomorphism"]
def uliftHom {A : CochainDGAlgebra.{u, v} R} {B : CochainDGAlgebra.{u, w} R}
    (f : CochainDGAlgebra.Hom A B) :
    CochainDGAlgebra.Hom (ulift.{u, v, l} A) (ulift.{u, w, l} B) where
  map n := uliftLinear.{u, v, w, l} (f.map n)
  comm_d := sorry
  map_one := sorry
  map_mul := sorry

/-- Lower a homomorphism between lifted cochain DGAs to the original carriers. -/
@[stacks 061X "lower a homomorphism between lifted cochain DGAs"]
def downHom {A : CochainDGAlgebra.{u, v} R} {B : CochainDGAlgebra.{u, w} R}
    (f : CochainDGAlgebra.Hom (ulift.{u, v, l} A) (ulift.{u, w, l} B)) :
    CochainDGAlgebra.Hom A B where
  map n :=
    { toFun := fun x ↦ (f.map n (ULift.up x)).down
      map_add' := sorry
      map_smul' := sorry }
  comm_d := sorry
  map_one := sorry
  map_mul := sorry

/-- Lowering a lifted DGA homomorphism evaluates by raising, applying the map, and lowering. -/
@[simp, stacks 061X "evaluation of a lowered cochain-DGA homomorphism"]
theorem downHom_apply {A : CochainDGAlgebra.{u, v} R} {B : CochainDGAlgebra.{u, w} R}
    (f : CochainDGAlgebra.Hom (ulift.{u, v, l} A) (ulift.{u, w, l} B))
    (n : ℤ) (x : A.X n) :
    (downHom.{u, v, w, l} f).map n x = (f.map n (ULift.up x)).down := sorry

/-- Lowering a lifted DGA homomorphism recovers the original homomorphism. -/
@[simp, stacks 061X "lower after lift for cochain-DGA homomorphisms"]
theorem downHom_uliftHom {A : CochainDGAlgebra.{u, v} R} {B : CochainDGAlgebra.{u, w} R}
    (f : CochainDGAlgebra.Hom A B) :
    downHom.{u, v, w, l} (uliftHom.{u, v, w, l} f) = f := sorry

/-- Lifting a lowered homomorphism between lifted DGAs recovers that homomorphism. -/
@[simp, stacks 061X "lift after lower for cochain-DGA homomorphisms"]
theorem uliftHom_downHom {A : CochainDGAlgebra.{u, v} R} {B : CochainDGAlgebra.{u, w} R}
    (f : CochainDGAlgebra.Hom (ulift.{u, v, l} A) (ulift.{u, w, l} B)) :
    uliftHom.{u, v, w, l} (downHom.{u, v, w, l} f) = f := sorry

/-- Universe lifting identifies DGA homomorphisms with homomorphisms between the lifted DGAs. -/
@[stacks 061X "hom-set equivalence for universe-lifted cochain DGAs"]
def uliftHomEquiv (A : CochainDGAlgebra.{u, v} R) (B : CochainDGAlgebra.{u, w} R) :
    CochainDGAlgebra.Hom A B ≃
      CochainDGAlgebra.Hom (ulift.{u, v, l} A) (ulift.{u, w, l} B) where
  toFun := uliftHom
  invFun := downHom
  left_inv := downHom_uliftHom
  right_inv := uliftHom_downHom

/-- The forward map of `uliftHomEquiv` is universe lifting of DGA homomorphisms. -/
@[simp, stacks 061X "forward map of the lifted cochain-DGA hom equivalence"]
theorem uliftHomEquiv_apply (A : CochainDGAlgebra.{u, v} R)
    (B : CochainDGAlgebra.{u, w} R) (f : CochainDGAlgebra.Hom A B) :
    uliftHomEquiv.{u, v, w, l} A B f = uliftHom.{u, v, w, l} f := sorry

/-- The inverse map of `uliftHomEquiv` lowers a homomorphism between lifted DGAs. -/
@[simp, stacks 061X "inverse map of the lifted cochain-DGA hom equivalence"]
theorem uliftHomEquiv_symm_apply (A : CochainDGAlgebra.{u, v} R)
    (B : CochainDGAlgebra.{u, w} R)
    (f : CochainDGAlgebra.Hom (ulift.{u, v, l} A) (ulift.{u, w, l} B)) :
    (uliftHomEquiv.{u, v, w, l} A B).symm f = downHom.{u, v, w, l} f := sorry

/-- Universe lifting is functorial on cochain differential graded algebras. -/
@[stacks 061X "universe-lift functor on cochain DGAs"]
def uliftFunctor :
    CochainDGAlgebra.{u, v} R ⥤ CochainDGAlgebra.{u, max v l} R where
  obj := ulift
  map f := uliftHom f
  map_id := sorry
  map_comp := sorry

/-- The DGA universe-lift functor uses `ulift` on objects. -/
@[simp, stacks 061X "cochain-DGA universe-lift functor on objects"]
theorem uliftFunctor_obj (A : CochainDGAlgebra.{u, v} R) :
    (uliftFunctor.{u, v, l} (R := R)).obj A = ulift.{u, v, l} A := sorry

/-- The DGA universe-lift functor uses `uliftHom` on morphisms. -/
@[simp, stacks 061X "cochain-DGA universe-lift functor on morphisms"]
theorem uliftFunctor_map {A B : CochainDGAlgebra.{u, v} R}
    (f : CochainDGAlgebra.Hom A B) :
    (uliftFunctor.{u, v, l} (R := R)).map f = uliftHom.{u, v, v, l} f := sorry

/-- The DGA universe-lift functor is fully faithful on morphisms. -/
@[stacks 061X "full faithfulness of the cochain-DGA universe lift"]
def fullyFaithfulUliftFunctor :
    (uliftFunctor.{u, v, l} (R := R)).FullyFaithful where
  preimage f := downHom f
  map_preimage := sorry
  preimage_map := sorry

/-- The cochain-DGA universe-lift functor is full. -/
@[stacks 061X "full instance for the cochain-DGA universe lift"]
instance uliftFunctorFull : (uliftFunctor.{u, v, l} (R := R)).Full := sorry

/-- The cochain-DGA universe-lift functor is faithful. -/
@[stacks 061X "faithful instance for the cochain-DGA universe lift"]
instance uliftFunctorFaithful : (uliftFunctor.{u, v, l} (R := R)).Faithful := sorry

/-- Degreewise carrier of a universe-lifted cochain DGA. -/
@[simp, stacks 061V "degreewise carrier of a lifted cochain DGA"]
theorem ulift_X (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    (ulift.{u, v, l} A).X n = (ModuleCat.uliftFunctor.{l} R).obj (A.X n) := sorry

/-- The lifted multiplication evaluates by lowering, multiplying, and raising. -/
@[simp, stacks 061V "evaluation of lifted DGA multiplication"]
theorem ulift_mul (A : CochainDGAlgebra.{u, v} R) (n m : ℤ)
    (x : (ulift.{u, v, l} A).X n) (y : (ulift.{u, v, l} A).X m) :
    (ulift.{u, v, l} A).mul n m x y = ULift.up (A.mul n m x.down y.down) := sorry

/-- The lifted unit is the raised original unit. -/
@[simp, stacks 061V "unit of a lifted cochain DGA"]
theorem ulift_one (A : CochainDGAlgebra.{u, v} R) :
    (ulift.{u, v, l} A).one = ULift.up A.one := sorry

/-- The differential of a lifted cochain DGA lowers, applies the original differential, and raises
again. -/
@[simp, stacks 061V "evaluation of a lifted DGA differential"]
theorem ulift_d_apply (A : CochainDGAlgebra.{u, v} R) (n : ℤ)
    (x : (ulift.{u, v, l} A).X n) :
    (ulift.{u, v, l} A).d n x = ULift.up (A.d n x.down) := sorry

/-- A lifted DGA homomorphism evaluates degreewise by lowering and raising. -/
@[simp, stacks 061X "evaluation of a lifted DGA homomorphism"]
theorem uliftHom_apply {A : CochainDGAlgebra.{u, v} R}
    {B : CochainDGAlgebra.{u, w} R} (f : CochainDGAlgebra.Hom A B)
    (n : ℤ) (x : (ulift.{u, v, l} A).X n) :
    (uliftHom.{u, v, w, l} f).map n x = ULift.up (f.map n x.down) := sorry

/-- The underlying complex of a lifted cochain DGA is the lifted original complex. -/
@[simp, stacks 061V "underlying complex of a lifted cochain DGA"]
theorem ulift_toCochainComplex (A : CochainDGAlgebra.{u, v} R) :
    (ulift.{u, v, l} A).toCochainComplex =
      ((ModuleCat.uliftFunctor.{l} R).mapHomologicalComplex (up ℤ)).obj
        A.toCochainComplex := sorry

end CochainDGAlgebra
