/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Single
public import Mathlib.RingTheory.TensorProduct.Basic
public import ReasLib.Algebra.Category.ModuleCat.TensorProduct
public import ReasLib.Algebra.Homology.CochainDGAlgebra.DegreeZero
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule

/-!
# Ordinary Bimodules as Differential Graded Bimodules

An ordinary left-`A`, right-`B` bimodule is a left module over `A ⊗[R] Bᵐᵒᵖ`.  This file
regards it as a differential graded `(A, B)`-bimodule supported in degree zero.  The action of
the DG enveloping algebra is defined explicitly from the ordinary pure-tensor action.  The ground
ring and the algebra/module carriers may live in different universes.
-/

@[expose] public section

noncomputable section

universe u uA uB

open CategoryTheory ComplexShape HomologicalComplex
open scoped TensorProduct

namespace DifferentialGradedBimodule.DegreeZero

variable {R : Type u} [CommRing R]
variable {A : Type uA} {B : Type uB} [Ring A] [Ring B] [Algebra R A] [Algebra R B]

/-- The underlying `R`-module of an ordinary left-`A`, right-`B` bimodule. -/
abbrev restrictedBimodule (N : ModuleCat.{max uA uB} (A ⊗[R] Bᵐᵒᵖ)) : ModuleCat.{max uA uB} R :=
  (ModuleCat.restrictScalars (algebraMap R (A ⊗[R] Bᵐᵒᵖ))).obj N

/-- The single-term cochain complex underlying an ordinary bimodule. -/
noncomputable abbrev complex (N : ModuleCat.{max uA uB} (A ⊗[R] Bᵐᵒᵖ)) :
    CochainComplex (ModuleCat.{max uA uB} R) ℤ :=
  (single (ModuleCat.{max uA uB} R) (up ℤ) 0).obj (restrictedBimodule N)

/-- The canonical identification of the degree-zero term with the underlying ordinary
bimodule. -/
noncomputable def zeroIso (N : ModuleCat.{max uA uB} (A ⊗[R] Bᵐᵒᵖ)) :
    (complex N).X 0 ≅ restrictedBimodule N :=
  singleObjXSelf (up ℤ) 0 (restrictedBimodule N)

/-- The ordinary action of a pure tensor `a ⊗ bᵒᵖ` on a degree-zero bimodule element. -/
noncomputable def pureActionCurried
    (N : ModuleCat.{max uA uB} (A ⊗[R] Bᵐᵒᵖ)) (x : (complex N).X 0) :
    (CochainDGAlgebra.ofAlgebra R A).opposite.X 0 →ₗ[R]
      (CochainDGAlgebra.ofAlgebra R B).X 0 →ₗ[R] (complex N).X 0 where
  toFun a :=
    { toFun := fun b ↦ (zeroIso N).inv
        ((_root_.TensorProduct.tmul R
          ((CochainDGAlgebra.ofAlgebraZeroIso R A).hom a)
          (MulOpposite.op ((CochainDGAlgebra.ofAlgebraZeroIso R B).hom b))) •
            (zeroIso N).hom x)
      map_add' := sorry
      map_smul' := sorry }
  map_add' := sorry
  map_smul' := sorry

/-- The pure-tensor action as a morphism from the tensor of the two degree-zero components. -/
noncomputable def pureAction
    (N : ModuleCat.{max uA uB} (A ⊗[R] Bᵐᵒᵖ)) (x : (complex N).X 0) :
    ModuleCat.Hom (ModuleCat.TensorProduct.obj R
        ((CochainDGAlgebra.ofAlgebra R A).opposite.X 0)
        ((CochainDGAlgebra.ofAlgebra R B).X 0))
      ((complex N).X 0) :=
  ModuleCat.TensorProduct.lift R (pureActionCurried N x)

/-- The summandwise action map defining the action of the degree-zero DG enveloping algebra. -/
noncomputable def actionComponent
    (N : ModuleCat.{max uA uB} (A ⊗[R] Bᵐᵒᵖ)) (x : (complex N).X 0) :
    (p q : ℤ) → (up ℤ).π (up ℤ) (up ℤ) (p, q) = 0 →
      ModuleCat.Hom (ModuleCat.TensorProduct.obj R
          ((CochainDGAlgebra.ofAlgebra R A).opposite.X p)
          ((CochainDGAlgebra.ofAlgebra R B).X q))
        ((complex N).X 0) :=
  fun p q ↦ match p, q with
    | 0, 0 => fun (_ : (up ℤ).π (up ℤ) (up ℤ) (0, 0) = 0) ↦
        pureAction N x
    | p, q => fun (_ : (up ℤ).π (up ℤ) (up ℤ) (p, q) = 0) ↦
      ModuleCat.ofHom
          (X := ModuleCat.TensorProduct.obj R
            ((CochainDGAlgebra.ofAlgebra R A).opposite.X p)
            ((CochainDGAlgebra.ofAlgebra R B).X q))
          (Y := (complex N).X 0) 0

/-- The degree-zero action of the DG enveloping algebra on an ordinary bimodule. -/
noncomputable def actionZero
    (N : ModuleCat.{max uA uB} (A ⊗[R] Bᵐᵒᵖ)) :
    (complex N).X 0 →ₗ[R]
      (CochainDGAlgebra.enveloping (CochainDGAlgebra.ofAlgebra R A)
        (CochainDGAlgebra.ofAlgebra R B)).X 0 →ₗ[R]
          (complex N).X 0 where
  toFun x :=
    (mapBifunctorDesc
      (A := (complex N).X 0) (j := 0)
      (K₁ := (CochainDGAlgebra.ofAlgebra R A).opposite.toCochainComplex)
      (K₂ := (CochainDGAlgebra.ofAlgebra R B).toCochainComplex)
      (F := ModuleCat.TensorProduct.functor.{u, uA, uB} R) (c := up ℤ)
      (actionComponent N x)).hom
  map_add' := sorry
  map_smul' := sorry

/-- The homogeneous DG-enveloping action on an ordinary bimodule supported in degree zero. -/
noncomputable def action
    (N : ModuleCat.{max uA uB} (A ⊗[R] Bᵐᵒᵖ)) : (p i : ℤ) →
    (complex N).X p →ₗ[R]
      (CochainDGAlgebra.enveloping (CochainDGAlgebra.ofAlgebra R A)
        (CochainDGAlgebra.ofAlgebra R B)).X i →ₗ[R]
          (complex N).X (p + i)
  | 0, 0 => actionZero N
  | _, _ => 0

/-- An ordinary left-`A`, right-`B` bimodule, regarded as a differential graded bimodule
supported in degree zero. -/
@[stacks 09SC "ordinary bimodule as a degree-zero differential graded bimodule"]
noncomputable def ofBimodule (N : ModuleCat.{max uA uB} (A ⊗[R] Bᵐᵒᵖ)) :
    DifferentialGradedBimodule.{u, max uA uB, uA, uB} (CochainDGAlgebra.ofAlgebra R A)
      (CochainDGAlgebra.ofAlgebra R B) where
  X := (complex N).X
  d n := ((complex N).d n (n + 1)).hom
  smul := action N
  d_sq := sorry
  smul_one := sorry
  smul_mul := sorry
  comm_d := sorry

/-- A morphism of ordinary left-`A`, right-`B` bimodules induces a morphism of their
degree-zero differential graded models. -/
noncomputable def ofBimoduleHom
    {N N' : ModuleCat.{max uA uB} (A ⊗[R] Bᵐᵒᵖ)} (f : N ⟶ N') :
    ofBimodule N ⟶ ofBimodule N' where
  hom n := (((single (ModuleCat.{max uA uB} R) (up ℤ) 0).map
    ((ModuleCat.restrictScalars (algebraMap R (A ⊗[R] Bᵐᵒᵖ))).map f)).f n).hom
  comm_d := sorry
  comm_smul := sorry

/-- The functor sending an ordinary left-`A`, right-`B` bimodule to its degree-zero
differential graded bimodule. -/
@[stacks 09SC "ordinary bimodules as degree-zero differential graded bimodules"]
noncomputable def ofBimoduleFunctor
    (R : Type u) [CommRing R] (A : Type uA) (B : Type uB) [Ring A] [Ring B]
    [Algebra R A] [Algebra R B] :
    ModuleCat.{max uA uB} (A ⊗[R] Bᵐᵒᵖ) ⥤
      DifferentialGradedBimodule.{u, max uA uB, uA, uB} (CochainDGAlgebra.ofAlgebra R A)
        (CochainDGAlgebra.ofAlgebra R B) where
  obj := ofBimodule
  map := ofBimoduleHom
  map_id := sorry
  map_comp := sorry

/-- The underlying graded object of `ofBimodule` is the single-term complex of the ordinary
bimodule. -/
@[simp]
theorem ofBimodule_X (N : ModuleCat.{max uA uB} (A ⊗[R] Bᵐᵒᵖ)) (n : ℤ) :
    (ofBimodule N).X n = (complex N).X n := sorry

/-- The degreewise map of `ofBimoduleHom` is the single-complex map induced after restriction
of scalars to `R`. -/
@[simp]
theorem ofBimoduleHom_hom
    {N N' : ModuleCat.{max uA uB} (A ⊗[R] Bᵐᵒᵖ)} (f : N ⟶ N') (n : ℤ) :
    (ofBimoduleHom f).hom n =
      (((single (ModuleCat.{max uA uB} R) (up ℤ) 0).map
        ((ModuleCat.restrictScalars (algebraMap R (A ⊗[R] Bᵐᵒᵖ))).map f)).f n).hom := sorry

/-- The degree-zero bimodule functor has `ofBimodule` as its object map. -/
@[simp]
theorem ofBimoduleFunctor_obj (N : ModuleCat.{max uA uB} (A ⊗[R] Bᵐᵒᵖ)) :
    (ofBimoduleFunctor R A B).obj N = ofBimodule N := sorry

/-- The degree-zero bimodule functor has `ofBimoduleHom` as its morphism map. -/
@[simp]
theorem ofBimoduleFunctor_map
    {N N' : ModuleCat.{max uA uB} (A ⊗[R] Bᵐᵒᵖ)} (f : N ⟶ N') :
    (ofBimoduleFunctor R A B).map f = ofBimoduleHom f := sorry

/-- Degree zero of `ofBimodule` is canonically the underlying ordinary bimodule. -/
@[stacks 09SC "degree-zero identification of an ordinary bimodule"]
noncomputable def ofBimoduleZeroIso (N : ModuleCat.{max uA uB} (A ⊗[R] Bᵐᵒᵖ)) :
    (ofBimodule N).X 0 ≅ restrictedBimodule N :=
  zeroIso N

/-- On a pure degree-zero enveloping tensor, `ofBimodule` acts by
`(a ⊗ bᵒᵖ) • x`. -/
@[simp]
theorem ofBimodule_smul_pure
    (N : ModuleCat.{max uA uB} (A ⊗[R] Bᵐᵒᵖ)) (x : (ofBimodule N).X 0)
    (a : (CochainDGAlgebra.ofAlgebra R A).opposite.X 0)
    (b : (CochainDGAlgebra.ofAlgebra R B).X 0) :
    (ofBimodule N).smul 0 0 x
        (CochainDGAlgebra.Enveloping.pure
          (CochainDGAlgebra.ofAlgebra R A) (CochainDGAlgebra.ofAlgebra R B) a b) =
      (ofBimoduleZeroIso N).inv
        ((_root_.TensorProduct.tmul R
          ((CochainDGAlgebra.ofAlgebraZeroIso R A).hom a)
          (MulOpposite.op ((CochainDGAlgebra.ofAlgebraZeroIso R B).hom b))) •
            (ofBimoduleZeroIso N).hom x) := sorry

end DifferentialGradedBimodule.DegreeZero
