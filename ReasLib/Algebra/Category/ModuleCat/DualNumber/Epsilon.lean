module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.DualNumber
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# The epsilon endomorphism of a dual-number module

This file owns restriction to the base ring and multiplication by `ε` on an arbitrary
dual-number module. The latter is exposed as a natural square-zero endomorphism, independently of
any presentation or quotient construction.
-/

universe u v

open CategoryTheory
open scoped DualNumber

namespace ModuleCat.DualNumber

variable {R : Type u} [CommRing R]

/-- Restriction of dual-number modules to modules over the base ring. -/
@[stacks 05CS "restriction functor to the base"]
noncomputable abbrev restrictFunctor : ModuleCat.{v} R[ε] ⥤ ModuleCat.{v} R :=
  ModuleCat.restrictScalars (algebraMap R R[ε])

/-- A dual-number module viewed as a module over the base ring. -/
@[stacks 05CS "restriction to the base"]
noncomputable abbrev restrict (M : ModuleCat.{v} R[ε]) : ModuleCat.{v} R :=
  restrictFunctor.obj M

/-- Multiplication by `ε` on an arbitrary module over the dual numbers. -/
@[stacks 05CS "epsilon endomorphism"]
def epsEnd (M : ModuleCat.{v} R[ε]) : M ⟶ M :=
  ModuleCat.ofHom (LinearMap.lsmul R[ε] M (ε : R[ε]))

/-- Multiplication by `ε` evaluates as the scalar action on the underlying module. -/
@[simp]
theorem epsEnd_apply (M : ModuleCat.{v} R[ε]) (x : M) :
    (epsEnd M).hom x = (ε : R[ε]) • x := rfl

/-- Multiplication by `ε` commutes with every morphism of dual-number modules. -/
theorem epsEnd_naturality {M N : ModuleCat.{v} R[ε]} (f : M ⟶ N) :
    f ≫ epsEnd N = epsEnd M ≫ f := by
  ext x
  exact (f.hom.map_smul (ε : R[ε]) x).symm

/-- Multiplication by `ε` commutes with the identity functor's action on morphisms of
dual-number modules. -/
theorem epsNatTrans_naturality {M N : ModuleCat.{v} R[ε]} (f : M ⟶ N) :
    (Functor.id (ModuleCat.{v} R[ε])).map f ≫ epsEnd N =
      epsEnd M ≫ (Functor.id (ModuleCat.{v} R[ε])).map f :=
  epsEnd_naturality f

/-- Multiplication by `ε` as a natural endomorphism of the identity functor on dual-number
modules. -/
@[stacks 05CS "epsilon natural transformation"]
def epsNatTrans :
    Functor.id (ModuleCat.{v} R[ε]) ⟶ Functor.id (ModuleCat.{v} R[ε]) where
  app := epsEnd (R := R)
  naturality := fun _ _ f => epsNatTrans_naturality (R := R) f

/-- Multiplication by `ε` is square-zero on every dual-number module. -/
@[simp, stacks 05CS "epsilon is square-zero"]
theorem epsEnd_sq (M : ModuleCat.{v} R[ε]) :
    epsEnd M ≫ epsEnd M = 0 := by
  ext x
  simp [epsEnd_apply, ← mul_smul]

/-- The natural epsilon endomorphism is square-zero. -/
@[simp]
theorem epsNatTrans_sq :
    epsNatTrans (R := R) ≫ epsNatTrans (R := R) = 0 := by
  ext M x
  simp [epsNatTrans]
  rfl

/-- Multiplication by `ε`, viewed as an endomorphism after restriction to the base ring. -/
@[stacks 05CS "restricted epsilon endomorphism"]
noncomputable def restrictedEpsEnd (M : ModuleCat.{v} R[ε]) : restrict M ⟶ restrict M :=
  restrictFunctor.map (epsEnd M)

/-- Restricted multiplication by `ε` has the same underlying action as multiplication by `ε`
before restriction of scalars. -/
@[simp]
theorem restrictedEpsEnd_apply (M : ModuleCat.{v} R[ε]) (x : M) :
    (restrictedEpsEnd M).hom x = (ε : R[ε]) • x := rfl

/-- Multiplication by `ε` remains square-zero after restriction to the base ring. -/
@[simp, stacks 05CS "restricted epsilon is square-zero"]
theorem restrictedEpsEnd_sq (M : ModuleCat.{v} R[ε]) :
    restrictedEpsEnd M ≫ restrictedEpsEnd M = 0 := by
  ext x
  simp [restrictedEpsEnd_apply, ← mul_smul]
  rfl

/-- On underlying linear maps, restricted multiplication by `ε` is square-zero. -/
@[simp]
theorem restrictedEpsEnd_hom_sq (M : ModuleCat.{v} R[ε]) :
    (restrictedEpsEnd M).hom.comp (restrictedEpsEnd M).hom = 0 := by
  ext x
  simp [restrictedEpsEnd_apply, ← mul_smul]
  rfl

/-- Restricted multiplication by `ε` commutes with every morphism of dual-number modules. -/
theorem restrictedEpsEnd_naturality {M N : ModuleCat.{v} R[ε]} (f : M ⟶ N) :
    restrictFunctor.map f ≫ restrictedEpsEnd N =
      restrictedEpsEnd M ≫ restrictFunctor.map f := by
  ext x
  exact (f.hom.map_smul (ε : R[ε]) x).symm

/-- Fully elaborated functor-map form of restricted epsilon naturality. -/
theorem restrictedEpsNatTrans_naturality
    {M N : ModuleCat.{v} R[ε]} (f : M ⟶ N) :
    (restrictFunctor (R := R)).map f ≫ restrictedEpsEnd (R := R) N =
      restrictedEpsEnd (R := R) M ≫ (restrictFunctor (R := R)).map f :=
  restrictedEpsEnd_naturality f

/-- Restricted multiplication by `ε` as a natural endomorphism of the restriction functor. -/
@[stacks 05CS "restricted epsilon natural transformation"]
noncomputable def restrictedEpsNatTrans :
    restrictFunctor (R := R) ⟶ restrictFunctor (R := R) where
  app := restrictedEpsEnd (R := R)
  naturality := fun _ _ f => restrictedEpsNatTrans_naturality (R := R) f

/-- The restricted natural epsilon endomorphism is square-zero. -/
@[simp]
theorem restrictedEpsNatTrans_sq :
    restrictedEpsNatTrans (R := R) ≫ restrictedEpsNatTrans (R := R) = 0 := by
  ext M x
  simp [restrictedEpsNatTrans]

end ModuleCat.DualNumber
