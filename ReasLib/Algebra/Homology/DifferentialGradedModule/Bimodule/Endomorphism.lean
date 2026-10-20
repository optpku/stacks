/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.Endomorphism
public import ReasLib.Algebra.Category.ModuleCat.TensorProduct
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule
public import ReasLib.Algebra.Homology.DifferentialGradedModule.DifferentialGraded

/-!
# Bimodule Actions and Endomorphism DGAs

A compatible left action on a fixed right differential graded module is represented intrinsically
by a DGA map into its endomorphism DGA in the differential graded category of right modules.
-/

@[expose] public section

noncomputable section

universe u v w x

open CategoryTheory
open DifferentialGradedCategory
open ComplexShape HomologicalComplex
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]
variable {B : CochainDGAlgebra.{u, w} R}

/-- The endomorphism DGA of a right differential graded `B`-module, formed in the differential
graded category `DGMod(B)`. -/
@[stacks 0FQI "endomorphism DGA of a right differential graded module"]
def endomorphismDGA (M : DifferentialGradedModule.{u, v} B) : CochainDGAlgebra.{u, v} R :=
  @DifferentialGradedCategory.endomorphismDGA R _
    (DifferentialGradedModule.{u, v} B) (differentialGradedCategory B) M

/-- Degree `n` of the endomorphism DGA is the module of degree-`n` right-`B`-linear maps. -/
@[stacks 0FQI "endomorphism DGA graded component"]
theorem endomorphismDGA_X (M : DifferentialGradedModule.{u, v} B) (n : ℤ) :
    M.endomorphismDGA.X n = ModuleCat.of R (GradedHom B M M n) := sorry

/-- The carrier equality underlying `endomorphismDGA_X`. -/
@[stacks 0FQI "carrier identification for the endomorphism DGA"]
theorem endomorphismDGATypeEq (M : DifferentialGradedModule.{u, v} B) (n : ℤ) :
    (M.endomorphismDGA.X n : Type v) = GradedHom B M M n := sorry

end DifferentialGradedModule

namespace DifferentialGradedBimodule

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, w} R} {B : CochainDGAlgebra.{u, x} R}

/-- A compatible differential graded left `A`-action on a fixed right differential graded
`B`-module. -/
@[stacks 09S9]
structure LeftAction (A : CochainDGAlgebra.{u, w} R)
    (M : DifferentialGradedModule.{u, v} B) where
  /-- The homogeneous left action `A^i × M^p ⟶ M^(i + p)`. -/
  leftMul (i p : ℤ) : A.X i →ₗ[R] M.X p →ₗ[R] M.X (i + p)
  /-- Multiplication in `A` acts by successive left actions. -/
  left_assoc (i j p : ℤ) (a : A.X i) (b : A.X j) (x : M.X p) :
    leftMul (i + j) p (A.mul i j a b) x =
      cast (congrArg (fun n : ℤ ↦ (M.X n : Type v)) (add_assoc i j p).symm)
        (leftMul i (j + p) a (leftMul j p b x))
  /-- The unit of `A` acts as the identity. -/
  one_left (p : ℤ) (x : M.X p) :
    leftMul 0 p A.one x =
      cast (congrArg (fun n : ℤ ↦ (M.X n : Type v)) (zero_add p).symm) x
  /-- The left `A`-action commutes with the right `B`-action. -/
  comm_right (i p j : ℤ) (a : A.X i) (x : M.X p) (b : B.X j) :
    cast (congrArg (fun n : ℤ ↦ (M.X n : Type v)) (add_assoc i p j))
        (M.smul (i + p) j (leftMul i p a x) b) =
      leftMul i (p + j) a (M.smul p j x b)
  /-- The differential satisfies the graded Leibniz rule for the left action. -/
  d_leftMul (i p : ℤ) (a : A.X i) (x : M.X p) :
    M.d (i + p) (leftMul i p a x) =
      cast
          (congrArg (fun n : ℤ ↦ (M.X n : Type v))
            (CochainDGAlgebra.leftLeibnizIndex i p))
          (leftMul (i + 1) p (A.d i a) x) +
        (i.negOnePow : R) •
          cast
            (congrArg (fun n : ℤ ↦ (M.X n : Type v))
              (CochainDGAlgebra.rightLeibnizIndex i p))
            (leftMul i (p + 1) a (M.d p x))

namespace LeftAction

variable {M : DifferentialGradedModule.{u, v} B}

/-- A compatible left action evaluates on homogeneous algebra and module elements. -/
@[stacks 0FQI "evaluation of a compatible left action"]
instance : CoeFun (LeftAction A M)
    (fun _ ↦ ∀ i p : ℤ, A.X i → M.X p → M.X (i + p)) where
  coe rho := fun i p a x ↦ rho.leftMul i p a x

/-- Coercion to a function is evaluation of the homogeneous left action. -/
@[stacks 0FQI "left action coercion evaluation", simp]
theorem coe_apply (rho : LeftAction A M) (i p : ℤ) (a : A.X i) (x : M.X p) :
    rho i p a x = rho.leftMul i p a x := sorry

/-- The degree-`i` right-`B`-linear endomorphism defined by a homogeneous left action. -/
@[stacks 0FQI "graded endomorphism induced by a left action"]
def toGradedHomValue (rho : LeftAction A M) (i : ℤ) (a : A.X i) :
    DifferentialGradedModule.GradedHom B M M i :=
  ⟨fun p ↦ ModuleCat.castLinearMap (congrArg M.X (add_comm i p)) (rho.leftMul i p a), sorry⟩

/-- The homogeneous endomorphism-DGA value defined by a compatible left action. -/
@[stacks 0FQI "endomorphism DGA value induced by a left action"]
def toEndomorphismValue (rho : LeftAction A M) (i : ℤ) (a : A.X i) :
    M.endomorphismDGA.X i :=
  cast (DifferentialGradedModule.endomorphismDGATypeEq M i).symm
    (rho.toGradedHomValue i a)

variable {M₀ : DifferentialGradedModule.{u, v} B}

/-- A compatible left action gives a DGA map into the endomorphism DGA in `DGMod(B)`. -/
@[stacks 0FQI "DGA map induced by a compatible left action"]
def toEndomorphismDGAHom (rho : LeftAction A M₀) :
    CochainDGAlgebra.Hom A M₀.endomorphismDGA where
  map i :=
    { toFun := rho.toEndomorphismValue i
      map_add' := sorry
      map_smul' := sorry }
  comm_d := sorry
  map_one := sorry
  map_mul := sorry

/-- Extract the degree-`i` right-`B`-linear map from a homogeneous endomorphism-DGA value. -/
@[stacks 0FQI "graded map extracted from an endomorphism DGA map"]
def ofEndomorphismGradedHom (tau : CochainDGAlgebra.Hom A M₀.endomorphismDGA)
    (i : ℤ) (a : A.X i) : DifferentialGradedModule.GradedHom B M₀ M₀ i :=
  cast (DifferentialGradedModule.endomorphismDGATypeEq M₀ i) (tau i a)

/-- The left-action value recovered from a DGA map into `End_{DGMod(B)}(M)`. -/
@[stacks 0FQI "left action value recovered from an endomorphism DGA map"]
def ofEndomorphismValue (tau : CochainDGAlgebra.Hom A M₀.endomorphismDGA)
    (i p : ℤ) (a : A.X i) (x : M₀.X p) : M₀.X (i + p) :=
  cast (congrArg (fun n : ℤ ↦ (M₀.X n : Type v)) (add_comm p i))
    (ofEndomorphismGradedHom tau i a p x)

/-- The recovered action by a fixed homogeneous algebra element as a linear map. -/
@[stacks 0FQI "right-linear action value recovered from an endomorphism DGA map"]
def ofEndomorphismRight (tau : CochainDGAlgebra.Hom A M₀.endomorphismDGA)
    (i p : ℤ) (a : A.X i) : M₀.X p →ₗ[R] M₀.X (i + p) where
  toFun := ofEndomorphismValue tau i p a
  map_add' := sorry
  map_smul' := sorry

/-- The homogeneous left action recovered from a DGA map into `End_{DGMod(B)}(M)`. -/
@[stacks 0FQI "left action map recovered from an endomorphism DGA map"]
def ofEndomorphismLeftMul (tau : CochainDGAlgebra.Hom A M₀.endomorphismDGA)
    (i p : ℤ) : A.X i →ₗ[R] M₀.X p →ₗ[R] M₀.X (i + p) where
  toFun := ofEndomorphismRight tau i p
  map_add' := sorry
  map_smul' := sorry

/-- Recover a compatible left action from a DGA map into the endomorphism DGA in `DGMod(B)`. -/
@[stacks 0FQI "left action recovered from an endomorphism DGA map"]
def ofEndomorphismDGAHom (tau : CochainDGAlgebra.Hom A M₀.endomorphismDGA) :
    LeftAction A M₀ where
  leftMul := ofEndomorphismLeftMul tau
  left_assoc := sorry
  one_left := sorry
  comm_right := sorry
  d_leftMul := sorry

/-- Lemma 22.28.2 (0FQI): compatible differential graded left `A`-actions on a fixed right
differential graded `B`-module `M` are equivalent to DGA maps
`CochainDGAlgebra.Hom A M.endomorphismDGA`. -/
@[stacks 0FQI "bimodule actions as maps to the endomorphism DGA"]
def equivEndomorphismDGAHom (A : CochainDGAlgebra.{u, w} R)
    (M : DifferentialGradedModule.{u, v} B) :
    LeftAction A M ≃ CochainDGAlgebra.Hom A M.endomorphismDGA where
  toFun := toEndomorphismDGAHom
  invFun := ofEndomorphismDGAHom
  left_inv := sorry
  right_inv := sorry

/-- The canonical equivalence sends a left action to its endomorphism-DGA map. -/
@[stacks 0FQI "forward map of the action-endomorphism equivalence", simp]
theorem equivEndomorphismDGAHom_apply (rho : LeftAction A M₀) :
    equivEndomorphismDGAHom A M₀ rho = rho.toEndomorphismDGAHom := sorry

/-- The inverse canonical equivalence recovers the homogeneous left action. -/
@[stacks 0FQI "inverse map of the action-endomorphism equivalence", simp]
theorem equivEndomorphismDGAHom_symm_apply
    (tau : CochainDGAlgebra.Hom A M₀.endomorphismDGA) :
    (equivEndomorphismDGAHom A M₀).symm tau = ofEndomorphismDGAHom tau := sorry

/-- A differential graded bimodule supplies a compatible left action on its underlying right
module. -/
@[stacks 0FQI "left action extracted from a DG bimodule"]
def ofBimodule (N : DifferentialGradedBimodule.{u, v, w, x} A B) :
    LeftAction A N.toRightModule where
  leftMul := N.leftMul
  left_assoc := sorry
  one_left := sorry
  comm_right := sorry
  d_leftMul := sorry

/-- Regard a compatible left action as a left differential graded module structure on the
fixed underlying complex. -/
@[stacks 0FQI "left DG module extracted from a compatible action"]
def toLeftModule (rho : LeftAction A M) : LeftDifferentialGradedModule.{u, v} A where
  X := M.X
  d := M.d
  smul := rho.leftMul
  d_sq := M.d_sq
  smul_one := sorry
  smul_mul := sorry
  comm_d := rho.d_leftMul

/-- The right `A.opposite`-module determined by a compatible left action. -/
@[stacks 0FQI "opposite right module induced by a compatible action"]
def toOppositeModule (rho : LeftAction A M) :
    DifferentialGradedModule.{u, v} A.opposite :=
  rho.toLeftModule.op

/-- Reassociation of the target degree for the action of a homogeneous enveloping tensor. -/
@[stacks 0FQI "degree reassociation for the enveloping action"]
theorem envelopingSmulDegree (p i j n : ℤ)
    (h : (up ℤ).π (up ℤ) (up ℤ) (i, j) = n) :
    (p + i) + j = p + n := sorry

/- The tensor lift and `mapBifunctorDesc` below place the underlying right module in the
enveloping carrier universe `max w x`; the carrier universes of `A` and `B` remain independent. -/
section EnvelopingCarrier

variable {M₀ : DifferentialGradedModule.{u, max w x} B}

/-- The action of a homogeneous pure tensor in `A.opposite ⊗[R] B`. -/
@[stacks 0FQI "pure tensor action on a DG bimodule"]
def envelopingSmulPure (rho : LeftAction A M₀) (p n i j : ℤ)
    (h : (up ℤ).π (up ℤ) (up ℤ) (i, j) = n)
    (x : M₀.X p) (a : A.opposite.X i) (b : B.X j) : M₀.X (p + n) :=
  cast (congrArg (fun k : ℤ ↦ (M₀.X k : Type (max w x)))
      (envelopingSmulDegree p i j n h))
    (M₀.smul (p + i) j (rho.toOppositeModule.smul p i x a) b)

/-- The action map of one homogeneous tensor summand of the enveloping DGA. -/
@[stacks 0FQI "homogeneous enveloping tensor action map"]
def envelopingSmulComponent (rho : LeftAction A M₀) (p n i j : ℤ)
    (h : (up ℤ).π (up ℤ) (up ℤ) (i, j) = n) (x : M₀.X p) :
    ModuleCat.TensorProduct.obj R (A.opposite.X i) (B.X j) ⟶
      M₀.X (p + n) :=
  ModuleCat.TensorProduct.liftOfBilinear R
    (fun a b ↦ envelopingSmulPure rho p n i j h x a b) sorry sorry sorry sorry

/-- The action of the full degree-`n` term of the enveloping DGA on a fixed homogeneous
module element. -/
@[stacks 0FQI "descended enveloping tensor action"]
def envelopingSmulDesc (rho : LeftAction A M₀) (p n : ℤ) (x : M₀.X p) :
    (CochainDGAlgebra.enveloping A B).X n ⟶ M₀.X (p + n) :=
  mapBifunctorDesc (K₁ := A.opposite.toCochainComplex) (K₂ := B.toCochainComplex)
    (F := ModuleCat.TensorProduct.functor.{u, w, x} R) (c := up ℤ)
    (fun i j h ↦ envelopingSmulComponent rho p n i j h x)

/-- The descended enveloping action is additive in the module input. -/
@[stacks 0FQI "additivity of the descended enveloping action"]
theorem envelopingSmulDesc_add (rho : LeftAction A M₀) (p n : ℤ) (x y : M₀.X p) :
    (envelopingSmulDesc rho p n (x + y)).hom =
      (envelopingSmulDesc rho p n x).hom + (envelopingSmulDesc rho p n y).hom := sorry

/-- The descended enveloping action is linear in the module input. -/
@[stacks 0FQI "linearity of the descended enveloping action"]
theorem envelopingSmulDesc_smul (rho : LeftAction A M₀) (p n : ℤ)
    (r : R) (x : M₀.X p) :
    (envelopingSmulDesc rho p n (r • x)).hom =
      r • (envelopingSmulDesc rho p n x).hom := sorry

/-- The right action of `A.opposite ⊗[R] B` determined by commuting left `A`- and right
`B`-actions. -/
@[stacks 0FQI "enveloping DGA action of a compatible left action"]
def envelopingSmul (rho : LeftAction A M₀) (p n : ℤ) :
    M₀.X p →ₗ[R] (CochainDGAlgebra.enveloping A B).X n →ₗ[R] M₀.X (p + n) where
  toFun := fun x ↦ (envelopingSmulDesc rho p n x).hom
  map_add' := envelopingSmulDesc_add rho p n
  map_smul' := envelopingSmulDesc_smul rho p n

/-- Package a compatible left action on a fixed right module as the corresponding differential
graded bimodule over the enveloping DGA. -/
@[stacks 0FQI "DG bimodule induced by a compatible left action"]
def toBimodule (rho : LeftAction A M₀) :
    DifferentialGradedBimodule.{u, max w x, w, x} A B where
  X := M₀.X
  d := M₀.d
  smul := rho.envelopingSmul
  d_sq := M₀.d_sq
  smul_one := sorry
  smul_mul := sorry
  comm_d := sorry

/-- Packaging a compatible left action preserves its fixed right differential graded module. -/
@[stacks 0FQI "right-module preservation under bimodule packaging", simp]
theorem toBimodule_toRightModule (rho : LeftAction A M₀) :
    rho.toBimodule.toRightModule = M₀ := sorry

/-- Packaging a compatible left action recovers the left module defined by that action. -/
@[stacks 0FQI "left-module preservation under bimodule packaging", simp]
theorem toBimodule_toLeftModule (rho : LeftAction A M₀) :
    rho.toBimodule.toLeftModule = rho.toLeftModule := sorry

/-- Extracting the left action of a bimodule and repackaging it recovers the bimodule. -/
@[stacks 0FQI "bimodule recovery from its left action", simp]
theorem toBimodule_ofBimodule
    (N : DifferentialGradedBimodule.{u, max w x, w, x} A B) :
    (ofBimodule N).toBimodule = N := sorry

/-- The intrinsic endomorphism-DGA map induced by a differential graded bimodule. -/
@[stacks 0FQI "endomorphism DGA map induced by a DG bimodule"]
def fromBimodule (N : DifferentialGradedBimodule.{u, max w x, w, x} A B) :
    CochainDGAlgebra.Hom A N.toRightModule.endomorphismDGA :=
  toEndomorphismDGAHom (ofBimodule N)

end EnvelopingCarrier

end LeftAction

end DifferentialGradedBimodule
