/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.InvertiblePower.Graded
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.TensorPower

/-!
# Pullbacks of integral powers of invertible scheme modules

The pullbacks of all integral powers of an invertible module carry the canonical unit and
multiplication induced by strong monoidality of module pullback.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules) [Invertible L]

/-- The degree-`n` object obtained by pulling back the `n`th integral power of an invertible
module. -/
noncomputable abbrev pullbackInvertiblePower (n : ℤ) : X.Modules :=
  (Scheme.Modules.pullback f).obj (tensorPowerInt L n)

/-- The pulled-back zeroth integral power is canonically the structure module. -/
noncomputable def pullbackInvertiblePowerZeroIso :
    pullbackInvertiblePower f L 0 ≅
      (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  (Scheme.Modules.pullback f).mapIso
      (@RingedSpace.InvertiblePower.zeroIso _ L
        (Invertible.ringedSpaceIsInvertible (inferInstance : Invertible L))) ≪≫
    (Scheme.Modules.pullback f).mapIso
      (RingedSpace.unitIsoTensorUnit Y.toRingedSpace) ≪≫
    pullbackUnitIso f ≪≫
    (RingedSpace.unitIsoTensorUnit X.toRingedSpace).symm

/-- The canonical unit section of the pulled-back zeroth integral power. -/
noncomputable def pullbackInvertiblePowerOne
    (U : (X.Opens)ᵒᵖ) : (pullbackInvertiblePower f L 0).val.obj U :=
  ((((pullbackInvertiblePowerZeroIso f L).inv).val.app U).hom)
    (1 : X.sheaf.obj.obj U)

/-- The canonical multiplication morphism between two pulled-back integral powers. -/
noncomputable def pullbackInvertiblePowerMulHom (m n : ℤ) :
    pullbackInvertiblePower f L m ⊗ pullbackInvertiblePower f L n ⟶
      pullbackInvertiblePower f L (m + n) :=
  pullbackTensorMap f
    (@RingedSpace.InvertiblePower.addIso _ L
      (Invertible.ringedSpaceIsInvertible (inferInstance : Invertible L)) m n).hom

/-- Multiplication of local sections of two pulled-back integral powers. -/
noncomputable def pullbackInvertiblePowerMul
    (U : (X.Opens)ᵒᵖ) (m n : ℤ) :
    (pullbackInvertiblePower f L m).val.obj U →ₗ[X.sheaf.obj.obj U]
      (pullbackInvertiblePower f L n).val.obj U →ₗ[X.sheaf.obj.obj U]
        (pullbackInvertiblePower f L (m + n)).val.obj U :=
  (tensorSectionLinear X.sheaf
      (pullbackInvertiblePower f L m) (pullbackInvertiblePower f L n) U).compr₂
    (((pullbackInvertiblePowerMulHom f L m n).val.app U).hom)

/-- The pulled-back unit section commutes with restriction maps. -/
theorem pullbackInvertiblePower_one_map {U V : (X.Opens)ᵒᵖ} (i : U ⟶ V) :
    ((pullbackInvertiblePower f L 0).val.map i).hom
        (pullbackInvertiblePowerOne f L U) =
      pullbackInvertiblePowerOne f L V := sorry

/-- Multiplication of pulled-back integral-power sections commutes with restriction maps. -/
theorem pullbackInvertiblePower_mul_map {U V : (X.Opens)ᵒᵖ} (i : U ⟶ V)
    (m n : ℤ) (x : (pullbackInvertiblePower f L m).val.obj U)
    (y : (pullbackInvertiblePower f L n).val.obj U) :
    ((pullbackInvertiblePower f L (m + n)).val.map i).hom
        (pullbackInvertiblePowerMul f L U m n x y) =
      pullbackInvertiblePowerMul f L V m n
        (((pullbackInvertiblePower f L m).val.map i).hom x)
        (((pullbackInvertiblePower f L n).val.map i).hom y) := sorry

/-- Multiplication of pulled-back integral-power sections is associative. -/
theorem pullbackInvertiblePower_mul_assoc
    (U : (X.Opens)ᵒᵖ) (i j k : ℤ)
    (a : (pullbackInvertiblePower f L i).val.obj U)
    (b : (pullbackInvertiblePower f L j).val.obj U)
    (c : (pullbackInvertiblePower f L k).val.obj U) :
    HEq
      (pullbackInvertiblePowerMul f L U (i + j) k
        (pullbackInvertiblePowerMul f L U i j a b) c)
      (pullbackInvertiblePowerMul f L U i (j + k) a
        (pullbackInvertiblePowerMul f L U j k b c)) := sorry

/-- The pulled-back degree-zero unit is a left identity. -/
theorem pullbackInvertiblePower_one_mul
    (U : (X.Opens)ᵒᵖ) (n : ℤ)
    (a : (pullbackInvertiblePower f L n).val.obj U) :
    HEq (pullbackInvertiblePowerMul f L U 0 n
      (pullbackInvertiblePowerOne f L U) a) a := sorry

/-- The pulled-back degree-zero unit is a right identity. -/
theorem pullbackInvertiblePower_mul_one
    (U : (X.Opens)ᵒᵖ) (n : ℤ)
    (a : (pullbackInvertiblePower f L n).val.obj U) :
    HEq (pullbackInvertiblePowerMul f L U n 0 a
      (pullbackInvertiblePowerOne f L U)) a := sorry

/-- The pulled-back integral powers of an invertible module form a graded algebra sheaf. -/
noncomputable def pullbackInvertiblePowerGradedAlgebra :
    GradedAlgebraSheaf.{u, u} X.sheaf ℤ where
  obj := pullbackInvertiblePower f L
  one := pullbackInvertiblePowerOne f L
  mul := pullbackInvertiblePowerMul f L
  map_one := pullbackInvertiblePower_one_map f L
  map_mul := pullbackInvertiblePower_mul_map f L
  mul_assoc := pullbackInvertiblePower_mul_assoc f L
  one_mul := pullbackInvertiblePower_one_mul f L
  mul_one := pullbackInvertiblePower_mul_one f L

end AlgebraicGeometry.Scheme.Modules
