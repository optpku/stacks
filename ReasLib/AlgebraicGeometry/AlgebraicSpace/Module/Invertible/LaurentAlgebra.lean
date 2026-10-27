/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.UniverseLift.Comparison
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Sections
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSiteTensorUnit
public import ReasLib.CategoryTheory.Monoidal.InvertiblePower
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.DirectSum.Ring

/-! # Laurent tensor algebras of invertible modules -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.ConcreteCategory CategoryTheory.Functor
open CategoryTheory.MonoidalCategory.InvertiblePower
open Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.IdealSubobject
open SheafOfModules.RingedSite SheafOfModules.RingedSite.ModuleSheafification
open RingedSite.ToposHom IsLocalRing TopologicalSpace
open scoped DirectSum TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

section

/-- Homogeneous sections of the integral tensor power of an invertible module. -/
abbrev tensorPowerSection (L : X.Modules) [isInvertibleObject L]
    (U : (smallEtaleSite X)ᵒᵖ) (n : ℤ) : Type u :=
  (InvertiblePower.obj L n).val.obj U

/-- The image of a structure-sheaf section in the monoidal unit of `X.Modules`. -/
noncomputable def tensorUnitSection (U : (smallEtaleSite X)ᵒᵖ)
    (r : (commStructureSheaf X).obj.obj U) :
    (𝟙_ X.Modules).val.obj U :=
  (((ofCommModules X).map
      (unitIsoTensorUnit (J := smallEtaleTopology X)
        (𝒪 := commStructureSheaf X)).hom).val.app U).hom r

/-- The sheaf-tensor section associated to a pair of homogeneous sections. -/
noncomputable def tensorPairSection (L : X.Modules) [isInvertibleObject L]
    (U : (smallEtaleSite X)ᵒᵖ) (m n : ℤ)
    (x : tensorPowerSection L U m) (y : tensorPowerSection L U n) :
    ((InvertiblePower.obj L m) ⊗ InvertiblePower.obj L n).val.obj U :=
  (RelativeProj.commTensorComparison (InvertiblePower.obj L m) (InvertiblePower.obj L n)).val.app U
    ((moduleSheafificationUnitToVal.{u + 1, u, u, u} (commStructureSheaf X)
        (PresheafOfModules.Monoidal.tensorObj
          ((toCommModules X).obj (InvertiblePower.obj L m)).val
          ((toCommModules X).obj (InvertiblePower.obj L n)).val)).app U
      (x ⊗ₜ y))

/-- Multiplication of homogeneous sections induced by `InvertiblePower.addIso`. -/
noncomputable def mulSection (L : X.Modules) [isInvertibleObject L]
    (U : (smallEtaleSite X)ᵒᵖ) (m n : ℤ)
    (x : tensorPowerSection L U m) (y : tensorPowerSection L U n) :
    tensorPowerSection L U (m + n) :=
  ((InvertiblePower.addIso L m n).hom.val.app U).hom (tensorPairSection L U m n x y)

/-- The canonical unit section of the zeroth integral tensor power. -/
noncomputable def oneSection (L : X.Modules) [isInvertibleObject L]
    (U : (smallEtaleSite X)ᵒᵖ) : tensorPowerSection L U 0 :=
  ((InvertiblePower.zeroIso L).inv.val.app U).hom (tensorUnitSection U 1)

variable (L : X.Modules) [isInvertibleObject L]
variable (U : (smallEtaleSite X)ᵒᵖ)

/-- Homogeneous multiplication on integral tensor-power sections. -/
instance instGMul : GradedMonoid.GMul (tensorPowerSection L U) where
  mul := fun {m n} => mulSection L U m n

/-- The degree-zero unit section. -/
instance instGOne : GradedMonoid.GOne (tensorPowerSection L U) where
  one := oneSection L U

/-- Graded monoid laws for integral tensor-power sections. -/
instance instGMonoid : GradedMonoid.GMonoid (tensorPowerSection L U) where
  one_mul := sorry
  mul_one := sorry
  mul_assoc := sorry

/-- Homogeneous sections of integral tensor powers commute. -/
instance instGCommMonoid : GradedMonoid.GCommMonoid (tensorPowerSection L U) where
  mul_comm := sorry

/-- Bilinear vanishing laws for homogeneous multiplication. -/
instance instGNonUnitalNonAssocSemiring :
    DirectSum.GNonUnitalNonAssocSemiring (tensorPowerSection L U) where
  mul_zero := sorry
  zero_mul := sorry
  mul_add := sorry
  add_mul := sorry

/-- Graded semiring structure on integral tensor-power sections. -/
instance instGSemiring : DirectSum.GSemiring (tensorPowerSection L U) where
  natCast n := n • GradedMonoid.GOne.one
  natCast_zero := sorry
  natCast_succ := sorry

/-- Graded commutative semiring structure on integral tensor-power sections. -/
instance instGCommSemiring : DirectSum.GCommSemiring (tensorPowerSection L U) where

/-- Graded ring structure on integral tensor-power sections. -/
instance instGRing : DirectSum.GRing (tensorPowerSection L U) where
  intCast z := z • GradedMonoid.GOne.one
  intCast_ofNat := sorry
  intCast_negSucc_ofNat := sorry

/-- Graded commutative ring structure on integral tensor-power sections. -/
instance instGCommRing : DirectSum.GCommRing (tensorPowerSection L U) where

/-- Restriction of a homogeneous tensor-power section along an étale morphism. -/
noncomputable def tensorPowerRestrict {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) (n : ℤ) :
    tensorPowerSection L U n →+ tensorPowerSection L V n :=
  ((InvertiblePower.obj L n).val.map i).hom.toAddMonoidHom

/-- Additive restriction of the integer-graded tensor-power DirectSum. -/
noncomputable def invertibleLaurentRestrict {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) :
    DirectSum ℤ (tensorPowerSection L U) →+ DirectSum ℤ (tensorPowerSection L V) :=
  DirectSum.map fun n => tensorPowerRestrict (L := L) (U := U) i n

/-- Ring restriction of the integer-graded tensor-power DirectSum. -/
noncomputable def invertibleLaurentRestrictRingHom {U V : (smallEtaleSite X)ᵒᵖ}
    (i : U ⟶ V) :
    DirectSum ℤ (tensorPowerSection L U) →+* DirectSum ℤ (tensorPowerSection L V) :=
  { invertibleLaurentRestrict (L := L) (U := U) i with
    map_one' := sorry
    map_mul' := sorry }

end

section

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The presheaf of integer-graded tensor-power algebras of an invertible module. -/
noncomputable def invertibleLaurentPresheaf (L : X.Modules) [isInvertibleObject L] :
    (smallEtaleSite X)ᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (DirectSum ℤ (tensorPowerSection L U))
  map i := CommRingCat.ofHom (invertibleLaurentRestrictRingHom (L := L) i)
  map_id := sorry
  map_comp := sorry

/-- The sheafification of the integer-graded tensor-power algebra of an invertible module. -/
noncomputable def invertibleLaurentSheaf (L : X.Modules) [isInvertibleObject L] :
    Sheaf (smallEtaleTopology X) CommRingCat.{u} :=
  (presheafToSheaf (smallEtaleTopology X) CommRingCat.{u}).obj
    (invertibleLaurentPresheaf L)

/-- The presheaf structure map from `𝒪_X` into the tensor-power DirectSum. -/
noncomputable def invertibleLaurentUnit (L : X.Modules) [isInvertibleObject L] :
    (commStructureSheaf X).obj ⟶ invertibleLaurentPresheaf L where
  app U :=
    CommRingCat.ofHom
      { toFun := fun r =>
          DirectSum.of (tensorPowerSection L U) 0
            (((InvertiblePower.zeroIso L).inv.val.app U).hom
              (tensorUnitSection U r))
        map_one' := sorry
        map_mul' := sorry
        map_zero' := sorry
        map_add' := sorry }
  naturality := sorry

/-- The canonical structure map from `𝒪_X` to the sheafified tensor-power algebra. -/
noncomputable def invertibleLaurentStructureMap (L : X.Modules) [isInvertibleObject L] :
    commStructureSheaf X ⟶ invertibleLaurentSheaf L :=
  CategoryTheory.Sheaf.homEquiv.symm
    (invertibleLaurentUnit L ≫
      toSheafify (smallEtaleTopology X) (invertibleLaurentPresheaf L))

/-- The tensor-power algebra of an invertible module, as an algebra under `𝒪_X`. -/
noncomputable def invertibleLaurentUnder (L : X.Modules) [isInvertibleObject L] :
    Under (commStructureSheaf X) :=
  Under.mk (invertibleLaurentStructureMap L)

/-- The underlying module of the tensor-power algebra is quasi-coherent. -/
theorem invertibleLaurent_isQuasicoherent (L : X.Modules) [isInvertibleObject L] :
    ((restrictionAlong (invertibleLaurentUnder L).hom).obj
      (unitModule (smallEtaleTopology X)
        (invertibleLaurentUnder L).right)).IsQuasicoherent :=
  sorry

/-- The quasi-coherent `𝒪_X`-algebra `⨁_{n ∈ ℤ} L^{⊗ n}`. -/
noncomputable def invertibleLaurentAlgebra (L : X.Modules) [isInvertibleObject L] :
    X.QcAlgebraUnder where
  obj := invertibleLaurentUnder L
  property := invertibleLaurent_isQuasicoherent L

/-- The underlying `𝒪_X`-module of the tensor-power algebra. -/
noncomputable def invertibleLaurentModule (L : X.Modules) [isInvertibleObject L] :
    X.Modules :=
  ofComm
    ((restrictionAlong (invertibleLaurentUnder L).hom).obj
      (unitModule (smallEtaleTopology X) (invertibleLaurentUnder L).right))

/-- Component of degree-`n` insertion at an étale object, as a morphism of
`𝒪_X`-modules. -/
noncomputable def degreeIncludeApp (L : X.Modules) [isInvertibleObject L] (n : ℤ)
    (U : (smallEtaleSite X)ᵒᵖ) :
    (InvertiblePower.obj L n).val.obj U ⟶ (invertibleLaurentModule L).val.obj U :=
  @ModuleCat.ofHom ((structureSheaf X).obj.obj U) _
    ((InvertiblePower.obj L n).val.obj U)
    ((invertibleLaurentModule L).val.obj U)
    ((InvertiblePower.obj L n).val.obj U).isAddCommGroup
    ((InvertiblePower.obj L n).val.obj U).isModule
    ((invertibleLaurentModule L).val.obj U).isAddCommGroup
    ((invertibleLaurentModule L).val.obj U).isModule
    { toFun := fun x =>
        ((toSheafify (smallEtaleTopology X) (invertibleLaurentPresheaf L)).app U).hom
          (DirectSum.of (tensorPowerSection L U) n x)
      map_add' := sorry
      map_smul' := sorry }

/-- Degree-`n` insertion of an invertible module into the tensor-power algebra. -/
noncomputable def degreeInclude (L : X.Modules) [isInvertibleObject L] (n : ℤ) :
    InvertiblePower.obj L n ⟶ invertibleLaurentModule L where
  val :=
    { app := fun U => degreeIncludeApp L n U
      naturality := sorry }

/-- Degree-one insertion of `L` into the tensor-power algebra. -/
noncomputable def degreeIncludeOne (L : X.Modules) [isInvertibleObject L] :
    L ⟶ invertibleLaurentModule L :=
  (InvertiblePower.oneIso L).inv ≫ degreeInclude L 1

end

end AlgebraicGeometry.AlgebraicSpace.Modules
