/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Quasicoherent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Commutative
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.TensorPower.Graded
public import stacks_project.Chap69.Lemma_69_13_2_IdealPower
public import stacks_project.Chap71.Definition_71_6_6_Sum
public import stacks_project.Chap71.Definition_71_7_1_AssociatedSheaf
public import stacks_project.Chap71.Lemma_71_11_11_Triple

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

namespace IdealSubobject

/-- The `n`th power of an ideal subobject of `𝒪_X`, as the ideal-power product
with the structure module. -/
noncomputable def pow {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (n : ℕ) : IdealSubobject X :=
  Modules.idealPowerProductSubobject I (SheafOfModules.unit (structureSheaf X)) n

/-- The `n`th power of an ideal subobject is the ideal-power product against
the structure module. -/
theorem pow_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (n : ℕ) :
    I.pow n =
      Modules.idealPowerProductSubobject I
        (SheafOfModules.unit (structureSheaf X)) n :=
  sorry

/-- The zeroth power of an ideal subobject is the unit ideal. -/
theorem pow_zero {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) : I.pow 0 = ⊤ :=
  sorry

/-- The successor power of an ideal subobject is the product with the previous
power. -/
theorem pow_succ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (n : ℕ) :
    I.pow (n + 1) = IdealSubobject.mul I (I.pow n) :=
  sorry

/-- The product of two powers of an ideal subobject is the power of the sum of
the exponents. -/
theorem mul_pow_add {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (n m : ℕ) :
    IdealSubobject.mul (I.pow n) (I.pow m) = I.pow (n + m) :=
  sorry

end IdealSubobject

/-- Natural-number powers of ideal subobjects of `𝒪_X`. -/
instance instPowIdealSubobject {S : Scheme.{u}} {X : AlgebraicSpace S} :
    Pow (IdealSubobject X) ℕ where
  pow := IdealSubobject.pow

namespace IsQuasiCoherent

/-- Powers of a quasi-coherent ideal sheaf are quasi-coherent. -/
instance instIsQuasiCoherent_pow {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [IsQuasiCoherent I] (n : ℕ) :
    IsQuasiCoherent (I.pow n) :=
  sorry

end IsQuasiCoherent

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
  sorry

/-- Negative Rees-algebra pieces are the zero ideal. -/
theorem reesAlgebraObj_negSucc {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (n : ℕ) :
    reesAlgebraObj I (Int.negSucc n) = (⊥ : IdealSubobject X).toModule :=
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- A negative left degree makes `reesAlgebraMul` the zero map. -/
theorem reesAlgebraMul_negSucc_left {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (U : (smallEtaleSite X)ᵒᵖ) (n : ℕ) (m : ℤ) :
    reesAlgebraMul I U (Int.negSucc n) m = 0 :=
  sorry

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
  sorry

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
  sorry

/-- The Rees algebra of a quasi-coherent ideal sheaf `I`, as the `ℤ`-graded
`𝒪_X`-algebra with nonnegative pieces `I ^ n`. -/
noncomputable def reesAlgebra {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [IsQuasiCoherent I] :
    GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X) ℤ where
  obj n := Modules.liftModule (reesAlgebraObj I n)
  one := reesAlgebraOne I
  mul := reesAlgebraMul I
  map_one := sorry
  map_mul := sorry
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry

/-- Nonnegative components of the Rees algebra are the lifts of `I ^ n`. -/
theorem reesAlgebra_obj_ofNat {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [IsQuasiCoherent I] (n : ℕ) :
    (reesAlgebra I).obj n = Modules.liftModule (I.pow n).toModule :=
  sorry

/-- Negative components of the Rees algebra are the lift of the zero ideal. -/
theorem reesAlgebra_obj_negSucc {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [IsQuasiCoherent I] (n : ℕ) :
    (reesAlgebra I).obj (Int.negSucc n) =
      Modules.liftModule (⊥ : IdealSubobject X).toModule :=
  sorry

/-- Universe lift of `I ^ n` recovers the degree-`n` piece of the Rees algebra. -/
noncomputable def reesAlgebraDegreePieceIso {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [IsQuasiCoherent I] (n : ℕ) :
    Modules.liftModule (I.pow n).toModule ≅ (reesAlgebra I) (Int.ofNat n) :=
  Iso.refl _

/-- `reesAlgebraDegreePieceIso` is the identity identification of `I ^ n` with
the corresponding Rees-algebra summand. -/
theorem reesAlgebraDegreePieceIso_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [IsQuasiCoherent I] (n : ℕ) :
    reesAlgebraDegreePieceIso I n =
      Iso.refl (Modules.liftModule (I.pow n).toModule) :=
  sorry

/-- Unlifted nonnegative pieces of the Rees algebra, with homogeneous
multiplication `I ^ n ⊗ I ^ m ⟶ I ^ (n + m)`. -/
noncomputable def reesDegreePieces {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [IsQuasiCoherent I] :
    RelativeProj.DegreePieces (reesAlgebra I) :=
  RelativeProj.DegreePieces.of (fun n ↦ (I.pow n).toModule)
    (fun n ↦ reesAlgebraDegreePieceIso I n) (fun i j ↦ reesDegreeMul I i j)
    (fun i j ↦ by
      -- Both sides are induced by the same ideal-power bilinear multiplication.
      sorry)

/-- The unlifted degree-`n` piece of `reesDegreePieces I` is `I ^ n`, with
homogeneous multiplication `reesDegreeMul`. -/
theorem reesDegreePieces_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [IsQuasiCoherent I] (n m : ℕ) :
    (reesDegreePieces I).obj n = (I.pow n).toModule ∧
      (reesDegreePieces I).mul n m = reesDegreeMul I n m :=
  sorry

/-- The Rees algebra of a quasi-coherent ideal sheaf is quasi-coherent in every
degree. -/
theorem reesAlgebra_isQuasicoherent {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [IsQuasiCoherent I] :
    GradedAlgebraSheaf.IsQuasicoherent.{u + 1, u} (reesAlgebra I) :=
  sorry

/-- The Rees algebra of a quasi-coherent ideal sheaf is commutative. -/
instance instIsCommutative_reesAlgebra {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [IsQuasiCoherent I] :
    (reesAlgebra I).IsCommutative :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
