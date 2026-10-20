/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Quasicoherent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Commutative
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.TensorPower.Graded
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSubobject.Power
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.UniverseLift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.UniverseLift.Morphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.Triple

/-!
# Rees algebras of quasi-coherent ideal sheaves on algebraic spaces

The Rees algebra of a quasi-coherent ideal sheaf `I` is the `ℤ`-graded
`𝒪_X`-algebra with degree `n` piece `I ^ n` for `n ≥ 0` and `0` for `n < 0`,
with homogeneous multiplication the image of the ideal-power action.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The degree-`n` piece of the Rees algebra of `I`, extended by zero in negative
degrees. -/
noncomputable def reesAlgebraObj {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (n : ℤ) : X.Modules :=
  match n with
  | Int.ofNat k => (I.pow k).toModule
  | Int.negSucc _ => (⊥ : IdealSubobject X).toModule

/-- Nonnegative Rees-algebra pieces are the corresponding ideal powers. -/
theorem reesAlgebraObj_ofNat {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (n : ℕ) :
    reesAlgebraObj I n = (I.pow n).toModule :=
  rfl

/-- Negative Rees-algebra pieces are the zero ideal. -/
theorem reesAlgebraObj_negSucc {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (n : ℕ) :
    reesAlgebraObj I (Int.negSucc n) = (⊥ : IdealSubobject X).toModule :=
  rfl

/-- The canonical multiplication morphism `I ^ n ⊗ I ^ m ⟶ I ^ n * I ^ m`,
obtained by factoring the structure-sheaf product through the image of the
ideal inclusions. -/
noncomputable def reesPowMulHom {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (n m : ℕ) :
    (I.pow n).toModule ⊗ (I.pow m).toModule ⟶
      (IdealSubobject.mul (I.pow n) (I.pow m)).toModule :=
  factorThruImageSubobject
    (Modules.action (I.pow n) (I.pow m).toModule ≫ (I.pow m).arrow)

/-- Homogeneous Rees multiplication is the image factorization of the
ideal-power action. -/
theorem reesPowMulHom_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (n m : ℕ) :
    reesPowMulHom I n m =
      factorThruImageSubobject
        (Modules.action (I.pow n) (I.pow m).toModule ≫ (I.pow m).arrow) :=
  rfl

/-- Homogeneous multiplication `I ^ n ⊗ I ^ m ⟶ I ^ (n + m)`, transporting the
image factorization along `I ^ n * I ^ m = I ^ (n + m)`. -/
noncomputable def reesDegreeMul {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (n m : ℕ) :
    (I.pow n).toModule ⊗ (I.pow m).toModule ⟶ (I.pow (n + m)).toModule :=
  reesPowMulHom I n m ≫
    eqToHom
      (congrArg (fun J : IdealSubobject X ↦ J.toModule)
        (IdealSubobject.mul_pow_add I n m))

/-- `reesDegreeMul` is `reesPowMulHom` transported along `mul_pow_add`. -/
theorem reesDegreeMul_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (n m : ℕ) :
    reesDegreeMul I n m =
      reesPowMulHom I n m ≫
        eqToHom
          (congrArg (fun J : IdealSubobject X ↦ J.toModule)
            (IdealSubobject.mul_pow_add I n m)) :=
  rfl

/-- Homogeneous multiplication of nonnegative lifted Rees pieces: the
universe-lifted tensor of `I ^ i` and `I ^ j`, compared into
`lift (I ^ i ⊗ I ^ j)` by `RelativeProj.liftModuleTensorApp`, then mapped by
`reesDegreeMul`. -/
noncomputable def reesAlgebraMulOfNat {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (U : (smallEtaleSite X)ᵒᵖ) (i j : ℕ) :
    (Modules.liftModule (I.pow i).toModule).val.obj U →ₗ[(commStructureSheafLift X).obj.obj U]
      (Modules.liftModule (I.pow j).toModule).val.obj U →ₗ[(commStructureSheafLift X).obj.obj U]
        (Modules.liftModule (I.pow (i + j)).toModule).val.obj U :=
  (RelativeProj.liftModuleTensorApp (I.pow i).toModule (I.pow j).toModule U).compr₂
    ((Modules.liftModuleMap (reesDegreeMul I i j)).val.app U).hom

/-- `reesAlgebraMulOfNat` is `liftModuleTensorApp` of the ideal-power modules
composed with `liftModuleMap` of `reesDegreeMul`. -/
theorem reesAlgebraMulOfNat_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (U : (smallEtaleSite X)ᵒᵖ) (i j : ℕ) :
    reesAlgebraMulOfNat I U i j =
      (RelativeProj.liftModuleTensorApp (I.pow i).toModule
          (I.pow j).toModule U).compr₂
        ((Modules.liftModuleMap (reesDegreeMul I i j)).val.app U).hom :=
  rfl

/-- Homogeneous multiplication of lifted Rees-algebra pieces: the product of
nonnegative pieces, and zero if either degree is negative. -/
noncomputable def reesAlgebraMul {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (U : (smallEtaleSite X)ᵒᵖ) (n m : ℤ) :
    (Modules.liftModule (reesAlgebraObj I n)).val.obj U →ₗ[(commStructureSheafLift X).obj.obj U]
      (Modules.liftModule (reesAlgebraObj I m)).val.obj U →ₗ[(commStructureSheafLift X).obj.obj U]
        (Modules.liftModule (reesAlgebraObj I (n + m))).val.obj U :=
  match n, m with
  | Int.ofNat i, Int.ofNat j => reesAlgebraMulOfNat I U i j
  | Int.negSucc _, _ => 0
  | Int.ofNat _, Int.negSucc _ => 0

/-- Nonnegative homogeneous multiplication of the Rees algebra is the lifted
ideal-power product. -/
theorem reesAlgebraMul_ofNat {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (U : (smallEtaleSite X)ᵒᵖ) (i j : ℕ) :
    reesAlgebraMul I U (Int.ofNat i) (Int.ofNat j) =
      reesAlgebraMulOfNat I U i j :=
  rfl

/-- A negative left degree makes `reesAlgebraMul` the zero map. -/
theorem reesAlgebraMul_negSucc_left {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (U : (smallEtaleSite X)ᵒᵖ) (n : ℕ) (m : ℤ) :
    reesAlgebraMul I U (Int.negSucc n) m = 0 :=
  rfl

/-- The canonical identification of the structure module with `I ^ 0`. -/
noncomputable def reesPowZeroHom {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) :
    SheafOfModules.unit (structureSheaf X) ⟶ (I.pow 0).toModule :=
  inv (⊤ : IdealSubobject X).arrow ≫
    eqToHom
      (congrArg (fun J : IdealSubobject X ↦ J.toModule)
        (IdealSubobject.pow_zero I).symm)

/-- `reesPowZeroHom` is the inverse of the unit-ideal inclusion, transported
to `I ^ 0`. -/
theorem reesPowZeroHom_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) :
    reesPowZeroHom I =
      inv (⊤ : IdealSubobject X).arrow ≫
        eqToHom
          (congrArg (fun J : IdealSubobject X ↦ J.toModule)
            (IdealSubobject.pow_zero I).symm) :=
  rfl

/-- The degree-zero unit section of the Rees algebra, obtained from the structure
sheaf unit along the inverse of `(I ^ 0).arrow`. -/
noncomputable def reesAlgebraOne {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (U : (smallEtaleSite X)ᵒᵖ) :
    (Modules.liftModule (reesAlgebraObj I 0)).val.obj U :=
  (((Modules.liftedUnitIso X).inv ≫
      Modules.liftModuleMap (reesPowZeroHom I)).val.app U).hom
    (TensorPower.oneSection (commStructureSheafLift X)
      (Modules.liftModule (SheafOfModules.unit (structureSheaf X))) U)

/-- The Rees-algebra unit is the structure-sheaf unit transported along
`(I ^ 0).arrow`. -/
theorem reesAlgebraOne_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (U : (smallEtaleSite X)ᵒᵖ) :
    reesAlgebraOne I U =
      (((Modules.liftedUnitIso X).inv ≫
          Modules.liftModuleMap (reesPowZeroHom I)).val.app U).hom
        (TensorPower.oneSection (commStructureSheafLift X)
          (Modules.liftModule (SheafOfModules.unit (structureSheaf X))) U) :=
  rfl

/-- The unit of the Rees algebra commutes with restriction of sections. -/
theorem reesAlgebra_map_one {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) {U V : (smallEtaleSite X)ᵒᵖ} (f : U ⟶ V) :
    ((Modules.liftModule (reesAlgebraObj I 0)).val.map f).hom
      (reesAlgebraOne I U) = reesAlgebraOne I V :=
  sorry

/-- Homogeneous Rees multiplication commutes with restriction of sections. -/
theorem reesAlgebra_map_mul {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) {U V : (smallEtaleSite X)ᵒᵖ} (f : U ⟶ V) (n m : ℤ)
    (a : (Modules.liftModule (reesAlgebraObj I n)).val.obj U)
    (b : (Modules.liftModule (reesAlgebraObj I m)).val.obj U) :
    ((Modules.liftModule (reesAlgebraObj I (n + m))).val.map f).hom
        (reesAlgebraMul I U n m a b) =
      reesAlgebraMul I V n m
        (((Modules.liftModule (reesAlgebraObj I n)).val.map f).hom a)
        (((Modules.liftModule (reesAlgebraObj I m)).val.map f).hom b) :=
  sorry

/-- Homogeneous multiplication in the Rees algebra is associative. -/
theorem reesAlgebra_mul_assoc {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (U : (smallEtaleSite X)ᵒᵖ) (i j k : ℤ)
    (a : (Modules.liftModule (reesAlgebraObj I i)).val.obj U)
    (b : (Modules.liftModule (reesAlgebraObj I j)).val.obj U)
    (c : (Modules.liftModule (reesAlgebraObj I k)).val.obj U) :
    HEq (reesAlgebraMul I U (i + j) k (reesAlgebraMul I U i j a b) c)
      (reesAlgebraMul I U i (j + k) a (reesAlgebraMul I U j k b c)) :=
  sorry

/-- The degree-zero unit is a left identity for homogeneous Rees multiplication. -/
theorem reesAlgebra_one_mul {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (U : (smallEtaleSite X)ᵒᵖ) (n : ℤ)
    (a : (Modules.liftModule (reesAlgebraObj I n)).val.obj U) :
    HEq (reesAlgebraMul I U 0 n (reesAlgebraOne I U) a) a :=
  sorry

/-- The degree-zero unit is a right identity for homogeneous Rees multiplication. -/
theorem reesAlgebra_mul_one {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (U : (smallEtaleSite X)ᵒᵖ) (n : ℤ)
    (a : (Modules.liftModule (reesAlgebraObj I n)).val.obj U) :
    HEq (reesAlgebraMul I U n 0 a (reesAlgebraOne I U)) a :=
  sorry

/-- The Rees algebra of a quasi-coherent ideal sheaf `I`, as the `ℤ`-graded
`𝒪_X`-algebra with nonnegative pieces `I ^ n`. -/
noncomputable def reesAlgebra {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [IsQuasiCoherent I] :
    GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X) ℤ where
  obj n := Modules.liftModule (reesAlgebraObj I n)
  one := reesAlgebraOne I
  mul := reesAlgebraMul I
  map_one := reesAlgebra_map_one I
  map_mul := reesAlgebra_map_mul I
  mul_assoc := reesAlgebra_mul_assoc I
  one_mul := reesAlgebra_one_mul I
  mul_one := reesAlgebra_mul_one I

/-- Nonnegative components of the Rees algebra are the lifts of `I ^ n`. -/
theorem reesAlgebra_obj_ofNat {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [IsQuasiCoherent I] (n : ℕ) :
    (reesAlgebra I).obj n = Modules.liftModule (I.pow n).toModule :=
  rfl

/-- Negative components of the Rees algebra are the lift of the zero ideal. -/
theorem reesAlgebra_obj_negSucc {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [IsQuasiCoherent I] (n : ℕ) :
    (reesAlgebra I).obj (Int.negSucc n) =
      Modules.liftModule (⊥ : IdealSubobject X).toModule :=
  rfl

/-- Universe lift of `I ^ n` recovers the degree-`n` piece of the Rees algebra. -/
noncomputable def reesAlgebraDegreePieceIso {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [IsQuasiCoherent I] (n : ℕ) :
    Modules.liftModule (I.pow n).toModule ≅ (reesAlgebra I).obj (Int.ofNat n) :=
  Iso.refl _

/-- `reesAlgebraDegreePieceIso` is the identity identification of `I ^ n` with
the corresponding Rees-algebra summand. -/
theorem reesAlgebraDegreePieceIso_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [IsQuasiCoherent I] (n : ℕ) :
    reesAlgebraDegreePieceIso I n =
      Iso.refl (Modules.liftModule (I.pow n).toModule) :=
  rfl

/-- The multiplication on ideal powers agrees with the lifted Rees multiplication
under the canonical degree-piece comparisons. -/
theorem reesDegreePieces_mul_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [IsQuasiCoherent I] (i j : ℕ) :
    RelativeProj.liftModuleTensorHom (I.pow i).toModule (I.pow j).toModule ≫
        Modules.liftModuleMap (reesDegreeMul I i j) =
      ((reesAlgebraDegreePieceIso I i).hom ⊗ₘ (reesAlgebraDegreePieceIso I j).hom) ≫
        GradedAlgebraSheaf.mulHom (reesAlgebra I) (Int.ofNat i) (Int.ofNat j) ≫
          eqToHom (congrArg (reesAlgebra I).obj (Int.natCast_add i j).symm) ≫
            (reesAlgebraDegreePieceIso I (i + j)).inv :=
  sorry

/-- Unlifted nonnegative pieces of the Rees algebra, with homogeneous
multiplication `I ^ n ⊗ I ^ m ⟶ I ^ (n + m)`. -/
noncomputable def reesDegreePieces {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [IsQuasiCoherent I] :
    RelativeProj.DegreePieces (reesAlgebra I) :=
  RelativeProj.DegreePieces.of (fun n ↦ (I.pow n).toModule)
    (fun n ↦ reesAlgebraDegreePieceIso I n) (fun i j ↦ reesDegreeMul I i j)
    (reesDegreePieces_mul_spec I)

/-- The unlifted degree-`n` piece of `reesDegreePieces I` is `I ^ n`, with
homogeneous multiplication `reesDegreeMul`. -/
theorem reesDegreePieces_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [IsQuasiCoherent I] (n m : ℕ) :
    (reesDegreePieces I).obj n = (I.pow n).toModule ∧
      (reesDegreePieces I).mul n m = reesDegreeMul I n m :=
  ⟨rfl, rfl⟩

/-- The Rees algebra of a quasi-coherent ideal sheaf is quasi-coherent in every
degree. -/
theorem reesAlgebra_isQuasicoherent {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [IsQuasiCoherent I] :
    GradedAlgebraSheaf.IsQuasicoherent.{u + 1, u} (reesAlgebra I) :=
  sorry

/-- The Rees algebra of a quasi-coherent ideal sheaf is commutative. -/
theorem reesAlgebra_isCommutative {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [IsQuasiCoherent I] :
    (reesAlgebra I).IsCommutative :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
