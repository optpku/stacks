module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Algebra
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Quasicoherent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Action
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Sections
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.RingedSpace
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Rees algebra of a quasi-coherent ideal sheaf on a scheme

The Rees algebra of a quasi-coherent ideal sheaf `I` on a scheme `Y` is the `ℤ`-graded
`𝒪_Y`-algebra with nonnegative pieces `I ^ n` and vanishing negative pieces, with homogeneous
multiplication induced by the ideal-power action.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {Y : Scheme.{u}}

/-- The degree-`n` piece of the Rees algebra of `I`, extended by zero in negative degrees. -/
noncomputable def reesAlgebraObj (I : Y.IdealSheafData) (n : ℤ) : Y.Modules :=
  match n with
  | Int.ofNat k => Scheme.Modules.fromRingedSpaceObj Y (I ^ k).toModule
  | Int.negSucc _ => Scheme.Modules.fromRingedSpaceObj Y (⊥ : Y.IdealSheafData).toModule

/-- Nonnegative Rees-algebra pieces are the corresponding ideal powers. -/
theorem reesAlgebraObj_ofNat (I : Y.IdealSheafData) (n : ℕ) :
    reesAlgebraObj I n = Scheme.Modules.fromRingedSpaceObj Y (I ^ n).toModule :=
  sorry

/-- Negative Rees-algebra pieces are the zero ideal. -/
theorem reesAlgebraObj_negSucc (I : Y.IdealSheafData) (n : ℕ) :
    reesAlgebraObj I (Int.negSucc n) =
      Scheme.Modules.fromRingedSpaceObj Y (⊥ : Y.IdealSheafData).toModule :=
  sorry



/-- The inclusion of an ideal power into the structure module, in the scheme-module
presentation. -/
noncomputable def reesArrow (I : Y.IdealSheafData) (n : ℕ) :
    reesAlgebraObj I n ⟶ (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) :=
  Scheme.Modules.fromRingedSpaceMap Y (I ^ n).toSubobject.arrow

/-- The image of the ideal-power action `I ^ n ⊗ I ^ m ⟶ 𝒪_Y` factors through `I ^ (n + m)`. -/
theorem reesPowMulHom_factors (I : Y.IdealSheafData) (n m : ℕ) :
    (I ^ (n + m)).toSubobject.Factors
      (Scheme.Modules.toRingedSpaceMap Y
        (IdealSheaf.action (I ^ n).toSubobject (reesAlgebraObj I m) ≫ reesArrow I m)) :=
  sorry

/-- Homogeneous multiplication `I ^ n ⊗ I ^ m ⟶ I ^ (n + m)`, obtained by factoring the
ideal-power action through `I ^ (n + m)`. -/
noncomputable def reesDegreeMul (I : Y.IdealSheafData) (n m : ℕ) :
    (reesAlgebraObj I n ⊗ reesAlgebraObj I m : Y.Modules) ⟶ reesAlgebraObj I (n + m) :=
  Scheme.Modules.fromRingedSpaceMap Y
    ((I ^ (n + m)).toSubobject.factorThru
      (Scheme.Modules.toRingedSpaceMap Y
        (IdealSheaf.action (I ^ n).toSubobject (reesAlgebraObj I m) ≫ reesArrow I m))
      (reesPowMulHom_factors I n m))


/-- Homogeneous multiplication of nonnegative Rees pieces on local sections. -/
noncomputable def reesAlgebraMulOfNat (I : Y.IdealSheafData) (U : (Opens Y)ᵒᵖ) (i j : ℕ) :
    (reesAlgebraObj I i).val.obj U →ₗ[Y.sheaf.obj.obj U]
      (reesAlgebraObj I j).val.obj U →ₗ[Y.sheaf.obj.obj U]
        (reesAlgebraObj I (i + j)).val.obj U :=
  (tensorSectionLinear Y.sheaf (reesAlgebraObj I i) (reesAlgebraObj I j) U).compr₂
    ((reesDegreeMul I i j).val.app U).hom


/-- Homogeneous multiplication of Rees-algebra pieces: the product of nonnegative pieces, and
zero if either degree is negative. -/
noncomputable def reesAlgebraMul (I : Y.IdealSheafData) (U : (Opens Y)ᵒᵖ) (n m : ℤ) :
    (reesAlgebraObj I n).val.obj U →ₗ[Y.sheaf.obj.obj U]
      (reesAlgebraObj I m).val.obj U →ₗ[Y.sheaf.obj.obj U]
        (reesAlgebraObj I (n + m)).val.obj U :=
  match n, m with
  | Int.ofNat i, Int.ofNat j => reesAlgebraMulOfNat I U i j
  | Int.negSucc _, _ => 0
  | Int.ofNat _, Int.negSucc _ => 0

/-- Nonnegative homogeneous multiplication of the Rees algebra is the ideal-power product. -/
theorem reesAlgebraMul_ofNat (I : Y.IdealSheafData) (U : (Opens Y)ᵒᵖ) (i j : ℕ) :
    reesAlgebraMul I U (Int.ofNat i) (Int.ofNat j) = reesAlgebraMulOfNat I U i j :=
  sorry

/-- A negative left degree makes `reesAlgebraMul` the zero map. -/
theorem reesAlgebraMul_negSucc_left (I : Y.IdealSheafData) (U : (Opens Y)ᵒᵖ) (n : ℕ) (m : ℤ) :
    reesAlgebraMul I U (Int.negSucc n) m = 0 :=
  sorry

/-- The identity of the structure module factors through `I ^ 0`. -/
theorem reesPowZeroHom_factors (I : Y.IdealSheafData) :
    (I ^ 0).toSubobject.Factors
      (Scheme.Modules.toRingedSpaceMap Y
        (𝟙 (SheafOfModules.unit Y.ringCatSheaf : Y.Modules))) :=
  sorry

/-- The canonical identification of the structure module with `I ^ 0`. -/
noncomputable def reesPowZeroHom (I : Y.IdealSheafData) :
    (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶ reesAlgebraObj I 0 :=
  Scheme.Modules.fromRingedSpaceMap Y
    ((I ^ 0).toSubobject.factorThru
      (Scheme.Modules.toRingedSpaceMap Y
        (𝟙 (SheafOfModules.unit Y.ringCatSheaf : Y.Modules)))
      (reesPowZeroHom_factors I))


/-- The degree-zero unit section of the Rees algebra, obtained from the structure-sheaf unit
along the inverse of `(I ^ 0).arrow`. -/
noncomputable def reesAlgebraOne (I : Y.IdealSheafData) (U : (Opens Y)ᵒᵖ) :
    (reesAlgebraObj I 0).val.obj U :=
  ((reesPowZeroHom I).val.app U).hom (1 : Y.sheaf.obj.obj U)


/-- Restriction of the Rees-algebra unit section. -/
theorem reesAlgebra_map_one (I : Y.IdealSheafData) {U V : (Opens Y)ᵒᵖ} (f : U ⟶ V) :
    ((reesAlgebraObj I 0).val.map f).hom (reesAlgebraOne I U) = reesAlgebraOne I V :=
  sorry

/-- Restriction of homogeneous Rees multiplication. -/
theorem reesAlgebra_map_mul (I : Y.IdealSheafData) {U V : (Opens Y)ᵒᵖ} (f : U ⟶ V)
    (n m : ℤ) (a : (reesAlgebraObj I n).val.obj U) (b : (reesAlgebraObj I m).val.obj U) :
    ((reesAlgebraObj I (n + m)).val.map f).hom (reesAlgebraMul I U n m a b) =
      reesAlgebraMul I V n m (((reesAlgebraObj I n).val.map f).hom a)
        (((reesAlgebraObj I m).val.map f).hom b) :=
  sorry

/-- Associativity of homogeneous Rees multiplication. -/
theorem reesAlgebra_mul_assoc (I : Y.IdealSheafData) (U : (Opens Y)ᵒᵖ) (i j k : ℤ)
    (a : (reesAlgebraObj I i).val.obj U) (b : (reesAlgebraObj I j).val.obj U)
    (c : (reesAlgebraObj I k).val.obj U) :
    HEq (reesAlgebraMul I U (i + j) k (reesAlgebraMul I U i j a b) c)
      (reesAlgebraMul I U i (j + k) a (reesAlgebraMul I U j k b c)) :=
  sorry

/-- The degree-zero unit is a left identity for Rees multiplication. -/
theorem reesAlgebra_one_mul (I : Y.IdealSheafData) (U : (Opens Y)ᵒᵖ) (n : ℤ)
    (a : (reesAlgebraObj I n).val.obj U) :
    HEq (reesAlgebraMul I U 0 n (reesAlgebraOne I U) a) a :=
  sorry

/-- The degree-zero unit is a right identity for Rees multiplication. -/
theorem reesAlgebra_mul_one (I : Y.IdealSheafData) (U : (Opens Y)ᵒᵖ) (n : ℤ)
    (a : (reesAlgebraObj I n).val.obj U) :
    HEq (reesAlgebraMul I U n 0 a (reesAlgebraOne I U)) a :=
  sorry

/-- The Rees algebra of a quasi-coherent ideal sheaf `I`, as the `ℤ`-graded `𝒪_Y`-algebra with
nonnegative pieces `I ^ n`. -/
noncomputable def reesAlgebra (I : Y.IdealSheafData) [I.toModule.IsQuasicoherent] :
    GradedAlgebraSheaf.{u, u} Y.sheaf ℤ where
  obj := reesAlgebraObj I
  one := reesAlgebraOne I
  mul := reesAlgebraMul I
  map_one := reesAlgebra_map_one I
  map_mul := reesAlgebra_map_mul I
  mul_assoc := reesAlgebra_mul_assoc I
  one_mul := reesAlgebra_one_mul I
  mul_one := reesAlgebra_mul_one I

/-- Nonnegative components of the Rees algebra are the corresponding ideal powers. -/
theorem reesAlgebra_obj_ofNat (I : Y.IdealSheafData) [I.toModule.IsQuasicoherent] (n : ℕ) :
    (reesAlgebra I).obj n = Scheme.Modules.fromRingedSpaceObj Y (I ^ n).toModule :=
  sorry

/-- Negative components of the Rees algebra are the zero ideal. -/
theorem reesAlgebra_obj_negSucc (I : Y.IdealSheafData) [I.toModule.IsQuasicoherent] (n : ℕ) :
    (reesAlgebra I).obj (Int.negSucc n) =
      Scheme.Modules.fromRingedSpaceObj Y (⊥ : Y.IdealSheafData).toModule :=
  sorry

/-- Every degree of the Rees algebra of a quasi-coherent ideal sheaf is quasi-coherent. -/
instance reesAlgebra_obj_isQuasicoherent (I : Y.IdealSheafData) [I.toModule.IsQuasicoherent]
    (n : ℤ) : ((reesAlgebra I).obj n).IsQuasicoherent :=
  sorry

end AlgebraicGeometry.Scheme.IdealSheafData
