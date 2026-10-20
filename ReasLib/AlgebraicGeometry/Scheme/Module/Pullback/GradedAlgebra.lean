/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Multiplication
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal

/-!
# Pullback of graded algebra sheaves on schemes

The strong-monoidal pullback of module sheaves transports the unit and multiplication of a
graded algebra sheaf degreewise.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.GradedAlgebra

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable {ι : Type} [AddMonoid ι] (𝒜 : GradedAlgebraSheaf.{u, u} Y.sheaf ι)

/-- The unit section in degree zero of the pullback of a graded algebra sheaf. -/
noncomputable def pullbackOne (U : (X.Opens)ᵒᵖ) :
    ((Scheme.Modules.pullback f).obj (𝒜 0)).val.obj U :=
  (((Scheme.Modules.pullback f).obj (𝒜 0)).unitHomEquiv
    ((RingedSpace.unitIsoTensorUnit X.toRingedSpace).hom ≫
      (pullbackUnitIso f).inv ≫
      (Scheme.Modules.pullback f).map
        (RingedSpace.unitIsoTensorUnit Y.toRingedSpace).inv ≫
      (Scheme.Modules.pullback f).map
        ((𝒜 0).unitHomEquiv.symm
          ((𝒜 0).val.sectionsMk 𝒜.one (fun _ _ g ↦ 𝒜.map_one g))))).1 U

/-- The multiplication morphism between two degrees of the pulled-back graded algebra. -/
noncomputable def pullbackMulHom (n m : ι) :
    (Scheme.Modules.pullback f).obj (𝒜 n) ⊗
        (Scheme.Modules.pullback f).obj (𝒜 m) ⟶
      (Scheme.Modules.pullback f).obj (𝒜 (n + m)) :=
  pullbackTensorMap f (GradedAlgebraSheaf.mulHom 𝒜 n m)

/-- Multiplication of local sections in the pullback of a graded algebra sheaf. -/
noncomputable def pullbackMul (U : (X.Opens)ᵒᵖ) (n m : ι) :
    ((Scheme.Modules.pullback f).obj (𝒜 n)).val.obj U →ₗ[X.sheaf.obj.obj U]
      ((Scheme.Modules.pullback f).obj (𝒜 m)).val.obj U →ₗ[X.sheaf.obj.obj U]
        ((Scheme.Modules.pullback f).obj (𝒜 (n + m))).val.obj U :=
  (tensorSectionLinear X.sheaf
      ((Scheme.Modules.pullback f).obj (𝒜 n))
      ((Scheme.Modules.pullback f).obj (𝒜 m)) U).compr₂
    (((pullbackMulHom f 𝒜 n m).val.app U).hom)

/-- The pulled-back unit section commutes with restriction maps. -/
theorem pullback_one_map {U V : (X.Opens)ᵒᵖ} (g : U ⟶ V) :
    (((Scheme.Modules.pullback f).obj (𝒜 0)).val.map g).hom
        (pullbackOne f 𝒜 U) =
      pullbackOne f 𝒜 V := sorry

/-- Multiplication of pulled-back homogeneous sections commutes with restriction maps. -/
theorem pullback_mul_map {U V : (X.Opens)ᵒᵖ} (g : U ⟶ V) (n m : ι)
    (a : ((Scheme.Modules.pullback f).obj (𝒜 n)).val.obj U)
    (b : ((Scheme.Modules.pullback f).obj (𝒜 m)).val.obj U) :
    (((Scheme.Modules.pullback f).obj (𝒜 (n + m))).val.map g).hom
        (pullbackMul f 𝒜 U n m a b) =
      pullbackMul f 𝒜 V n m
        ((((Scheme.Modules.pullback f).obj (𝒜 n)).val.map g).hom a)
        ((((Scheme.Modules.pullback f).obj (𝒜 m)).val.map g).hom b) := sorry

/-- Multiplication in the pulled-back graded algebra is associative. -/
theorem pullback_mul_assoc (U : (X.Opens)ᵒᵖ) (i j k : ι)
    (a : ((Scheme.Modules.pullback f).obj (𝒜 i)).val.obj U)
    (b : ((Scheme.Modules.pullback f).obj (𝒜 j)).val.obj U)
    (c : ((Scheme.Modules.pullback f).obj (𝒜 k)).val.obj U) :
    HEq
      (pullbackMul f 𝒜 U (i + j) k (pullbackMul f 𝒜 U i j a b) c)
      (pullbackMul f 𝒜 U i (j + k) a (pullbackMul f 𝒜 U j k b c)) := sorry

/-- The degree-zero unit of the pulled-back graded algebra is a left identity. -/
theorem pullback_one_mul (U : (X.Opens)ᵒᵖ) (n : ι)
    (a : ((Scheme.Modules.pullback f).obj (𝒜 n)).val.obj U) :
    HEq (pullbackMul f 𝒜 U 0 n (pullbackOne f 𝒜 U) a) a := sorry

/-- The degree-zero unit of the pulled-back graded algebra is a right identity. -/
theorem pullback_mul_one (U : (X.Opens)ᵒᵖ) (n : ι)
    (a : ((Scheme.Modules.pullback f).obj (𝒜 n)).val.obj U) :
    HEq (pullbackMul f 𝒜 U n 0 a (pullbackOne f 𝒜 U)) a := sorry

/-- Pullback of a graded algebra sheaf along a scheme morphism. -/
noncomputable def pullback : GradedAlgebraSheaf.{u, u} X.sheaf ι where
  obj n := (Scheme.Modules.pullback f).obj (𝒜 n)
  one := pullbackOne f 𝒜
  mul := pullbackMul f 𝒜
  map_one := pullback_one_map f 𝒜
  map_mul := pullback_mul_map f 𝒜
  mul_assoc := pullback_mul_assoc f 𝒜
  one_mul := pullback_one_mul f 𝒜
  mul_one := pullback_mul_one f 𝒜

end AlgebraicGeometry.Scheme.Modules.GradedAlgebra
