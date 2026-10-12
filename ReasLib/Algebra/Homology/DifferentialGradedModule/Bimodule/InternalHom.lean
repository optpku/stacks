/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.Functor
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.Endomorphism
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Endomorphism.Right

/-!
# Internal Hom from a Differential Graded Bimodule

For a differential graded `(A, B)`-bimodule `N`, this file constructs the right differential
graded `A`-module of homogeneous right-`B`-linear maps from `N` and the resulting fixed-source
DG functor `DGMod(B) -> DGMod(A)`.
-/

@[expose] public section

noncomputable section

universe u v w x

open CategoryTheory
open DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace DifferentialGradedBimodule

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, w} R} {B : CochainDGAlgebra.{u, x} R}

/-- The degree-`k` term of the internal Hom from `N` to `P`. -/
@[stacks 09LG "graded components of the fixed-source internal Hom"]
abbrev internalHomFamily (N : DifferentialGradedBimodule A B)
    (P : DifferentialGradedModule.{u, v} B) (k : ℤ) : ModuleCat.{v} R :=
  ModuleCat.of R (DifferentialGradedModule.GradedHom B N.toRightModule P k)

/-- The standard differential on the fixed-source internal Hom. -/
@[stacks 09LG "differential of the fixed-source internal Hom"]
def internalHomDifferential (N : DifferentialGradedBimodule A B)
    (P : DifferentialGradedModule.{u, v} B) (k : ℤ) :
    internalHomFamily N P k →ₗ[R] internalHomFamily N P (k + 1) where
  toFun := DifferentialGradedModule.gradedHomDifferential k
  map_add' := sorry
  map_smul' := sorry

/-- Precomposition by the left `A`-action on `N`, regarded as an action of `Aᵒᵖ` on the
fixed-source internal Hom. -/
@[stacks 09LG "left action on the fixed-source internal Hom"]
def internalHomAction (N : DifferentialGradedBimodule A B)
    (P : DifferentialGradedModule.{u, v} B) :
    EndomorphismDGAHom A.opposite (internalHomFamily N P) (internalHomDifferential N P) where
  map i :=
    { toFun := fun a p ↦
        { toFun := fun f ↦ (CochainDGAlgebra.oppositeSign R i p) •
              DifferentialGradedModule.gradedHomComp f
                ((LeftAction.ofBimodule N).toGradedHomValue i a)
          map_add' := sorry
          map_smul' := sorry }
      map_add' := sorry
      map_smul' := sorry }
  d_sq := sorry
  map_one := sorry
  map_mul := sorry
  comm_d := sorry

/-- The internal Hom right differential graded `A`-module represented by the bimodule `N`. -/
@[stacks 09LG "fixed-source internal Hom differential graded module"]
def internalHom (N : DifferentialGradedBimodule A B)
    (P : DifferentialGradedModule.{u, v} B) : DifferentialGradedModule.{u, v} A :=
  (DifferentialGradedModule.WithFixedUnderlying.ofEndomorphismDGAHom
    (internalHomAction N P)).toRightDifferentialGradedModule

/-- Degree `k` of `internalHom N P` is the module of degree-`k` right-`B`-linear maps. -/
theorem internalHom_X (N : DifferentialGradedBimodule A B)
    (P : DifferentialGradedModule.{u, v} B) (k : ℤ) :
    (internalHom N P).X k = internalHomFamily N P k := sorry

/-- The differential of `internalHom N P` is the graded commutator differential. -/
theorem internalHom_d (N : DifferentialGradedBimodule A B)
    (P : DifferentialGradedModule.{u, v} B) (k : ℤ) :
    (internalHom N P).d k = internalHomDifferential N P k := sorry

/-- Reassociation used when evaluating the sign-free precomposition action. -/
theorem internalHomActionDegree (i q p : ℤ) :
    (i + q) + p = q + (p + i) := sorry

/-- View a homogeneous element of the internal-Hom module as its right-`B`-linear graded map. -/
abbrev asGradedHom (N : DifferentialGradedBimodule A B)
    (P : DifferentialGradedModule.{u, v} B) {k : ℤ}
    (f : (internalHom N P).X k) :
    DifferentialGradedModule.GradedHom B N.toRightModule P k :=
  f

/-- The right `A`-action on internal Hom is precomposition by the left action on `N`, with no
sign in the resulting module formula. -/
theorem internalHom_smul_apply (N : DifferentialGradedBimodule A B)
    (P : DifferentialGradedModule.{u, v} B) (p i q : ℤ)
    (f : DifferentialGradedModule.GradedHom B N.toRightModule P p)
    (a : A.X i) (x : N.X q) :
    asGradedHom N P ((internalHom N P).smul p i f a) q x =
      cast (congrArg (fun n : ℤ ↦ (P.X n : Type v)) (internalHomActionDegree i q p))
        (f (i + q) (N.leftMul i q a x)) := sorry

/-- Postcomposition by a homogeneous right-`B`-linear map on the target internal Hom. -/
@[stacks 09LG "postcomposition map on the fixed-source internal Hom"]
def internalHomMap (N : DifferentialGradedBimodule A B)
    {P Q : DifferentialGradedModule.{u, v} B} {j : ℤ}
    (g : DifferentialGradedModule.GradedHom B P Q j) :
    DifferentialGradedModule.GradedHom A (internalHom N P) (internalHom N Q) j :=
  ⟨fun p ↦
      { toFun := fun f ↦ DifferentialGradedModule.gradedHomComp g f
        map_add' := sorry
        map_smul' := sorry },
    sorry⟩

/-- Evaluating the internal-Hom map is homogeneous postcomposition. -/
theorem internalHomMap_apply (N : DifferentialGradedBimodule A B)
    {P Q : DifferentialGradedModule.{u, v} B} {j p : ℤ}
    (g : DifferentialGradedModule.GradedHom B P Q j)
    (f : DifferentialGradedModule.GradedHom B N.toRightModule P p) :
    internalHomMap N g p f = DifferentialGradedModule.gradedHomComp g f := sorry

/-- Fixed-source internal Hom sends closed homogeneous target maps to closed homogeneous maps. -/
@[stacks 09LG "closed postcomposition map on the fixed-source internal Hom"]
def internalHomMapClosed (N : DifferentialGradedBimodule A B)
    {P Q : DifferentialGradedModule.{u, v} B} {j : ℤ}
    (g : DifferentialGradedModule.ClosedGradedHom B P Q j) :
    DifferentialGradedModule.ClosedGradedHom A (internalHom N P) (internalHom N Q) j :=
  ⟨internalHomMap N g.1, sorry⟩

/-- Equation 22.31.0.1 (09LG): fixed-source internal Hom is a concrete differential graded
functor from right DG `B`-modules to right DG `A`-modules. -/
@[stacks 09LG "internal Hom DG functor", stacks 0FQQ]
def internalHomDgFunctor (N : DifferentialGradedBimodule A B) :
    DgFunctor R (DifferentialGradedModule.{u, v} B)
      (DifferentialGradedModule.{u, v} A) where
  obj := internalHom N
  map := internalHomMap N
  map_add := sorry
  map_smul := sorry
  map_d := sorry
  map_id := sorry
  map_comp := sorry

/-- The fixed-source internal-Hom DG functor uses `internalHom` on objects. -/
theorem internalHomDgFunctor_obj (N : DifferentialGradedBimodule A B)
    (P : DifferentialGradedModule.{u, v} B) :
    (internalHomDgFunctor N).obj P = internalHom N P := sorry

/-- The fixed-source internal-Hom DG functor uses homogeneous postcomposition on maps. -/
theorem internalHomDgFunctor_map (N : DifferentialGradedBimodule A B)
    {P Q : DifferentialGradedModule.{u, v} B} {j : ℤ}
    (g : P ⟶[j] Q) :
    (internalHomDgFunctor N).map g = internalHomMap N g := sorry

end DifferentialGradedBimodule
