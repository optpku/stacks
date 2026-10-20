/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Monoidal
public import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.Tactic.CrossRefAttribute

/-!
# The unit object for canonical module `RHom`

The degree-zero regular module is the source-facing unit object.  This leaf owns its concrete
object and scalar maps, and it also provides the right-adjoint transport which turns an *explicit*
comparison between derived tensoring by that object and the identity into an `RHom` unit
isomorphism.  The comparison is intentionally an input: a closed presentation alone does not
choose a derived tensor-unit isomorphism.
@stack 0E1U
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.MonoidalCategory

namespace CategoryTheory.DerivedCategory.InternalHom.RHom.Unit

variable {A : Type u} [CommRing A]

/-- 0E1U: The regular module placed in degree zero in `D(A)`. -/
@[stacks 0E1U "degree-zero regular derived module"]
noncomputable abbrev single : DerivedCategory (ModuleCat A) :=
  ModuleCat.single0 (ModuleCat.of A A)

/- The scalar endomorphism is kept concrete, so downstream statements need not reconstruct the
  degree-zero single functor or the free-rank-one module map. -/
/-- 0E1U: Multiplication by `a` induces the corresponding map on the regular degree-zero object. -/
@[stacks 0E1U "regular degree-zero scalar map"]
noncomputable abbrev singleMap (a : A) :
    single (A := A) ⟶ single (A := A) :=
  ModuleCat.single0Functor.map (ModuleCat.ofHom (LinearMap.mulRight A a))

/-- 0E1U: The regular degree-zero map given by multiplication is scalar multiplication on the object. -/
@[simp, stacks 0E1U "regular degree-zero scalar map"]
theorem singleMap_eq_smul (a : A) :
    singleMap (A := A) a = a • 𝟙 (single (A := A)) := by
  change
    ModuleCat.single0Functor.map
        (ModuleCat.ofHom (LinearMap.mulRight A a)) =
      a • 𝟙 (ModuleCat.single0Functor.obj (ModuleCat.of A A))
  rw [← ModuleCat.single0Functor.map_id, ← Functor.map_smul]
  congr 1
  ext
  simp [LinearMap.mulRight_apply, mul_comm]

section Tensor

variable [MonoidalCategory (DerivedCategory (ModuleCat A))]

/-- 0E1U: Compare canonical fixed-right derived tensoring by `A[0]` with the identity from an explicit
tensor model and an explicit identification of `A[0]` with the ambient tensor unit. -/
@[stacks 0E1U "derived tensor comparison for the regular unit"]
noncomputable def tensorUnitComparisonOf
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat A))
    (s : single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat A))) :
    DerivedTensor.Right.functor (single (A := A)) ≅
      𝟭 (DerivedCategory (ModuleCat A)) :=
  T.functorIsoUnit (single (A := A)) s

/-- 0E1U: The objectwise regular-module comparison supplied by an explicit tensor-unit model. -/
@[stacks 0E1U "regular degree-zero derived tensor unit object comparison"]
noncomputable abbrev single0DerivedTensorIso
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat A))
    (s : single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat A)))
    (K : DerivedCategory (ModuleCat A)) [DerivedTensor.Right.Has (C := ModuleCat A)] :
    DerivedTensor.Right.obj K (single (A := A)) ≅ K :=
  (tensorUnitComparisonOf (A := A) T s).app K

end Tensor

section RHom

variable [RHom.Has (A := A)]

/-- 0E1U: Precomposition on `RHom(A[0], -)` induced by multiplication on the regular module. -/
@[stacks 0E1U "regular degree-zero RHom precomposition"]
noncomputable abbrev singlePre (a : A) :
    RHom.targetFunctor (A := A) (single (A := A)) ⟶
      RHom.targetFunctor (A := A) (single (A := A)) :=
  RHom.pre (A := A) (singleMap (A := A) a)

/-- 0E1U: The component of regular degree-zero `RHom` precomposition is the canonical two-variable map. -/
@[stacks 0E1U "regular degree-zero RHom precomposition component"]
theorem singlePre_app (a : A) (K : DerivedCategory (ModuleCat A)) :
    (singlePre (A := A) a).app K =
      RHom.map (A := A) (singleMap (A := A) a) (𝟙 K) :=
  RHom.pre_app (singleMap (A := A) a) K

/-- 0E1U: Precomposition by multiplication on `A[0]` acts by the same scalar on canonical `RHom`. -/
@[simp, stacks 0E1U "regular degree-zero RHom scalar action"]
theorem singlePre_app_eq_smul (a : A) (K : DerivedCategory (ModuleCat A)) :
    (singlePre (A := A) a).app K =
      a • 𝟙 (RHom.obj (A := A) (single (A := A)) K) := by
  rw [singlePre_app, ← RHom.sourceFunctor_map, singleMap_eq_smul, op_smul,
    Functor.map_smul, RHom.sourceFunctor_map, RHom.map_id]
  rfl

/-- Transport an explicit tensor-unit comparison to a canonical `RHom` unit isomorphism.

The argument `adj` is the selected canonical-RHom adjunction at `A[0]`, and `e` is the comparison
`- ⊗ᴸ A[0] ≅ 𝟭`.  Keeping both inputs pointwise and explicit prevents an ambient closed instance
from silently becoming a computational claim about derived tensoring.
-/
@[stacks 0E1U "canonical RHom unit from explicit tensor-unit comparison"]
noncomputable def targetIsoOf
    (adj : DerivedTensor.Right.functor (single (A := A)) ⊣
      RHom.targetFunctor (A := A) (single (A := A)))
    (e : DerivedTensor.Right.functor (single (A := A)) ≅
      𝟭 (DerivedCategory (ModuleCat A))) :
    RHom.targetFunctor (A := A) (single (A := A)) ≅
      𝟭 (DerivedCategory (ModuleCat A)) :=
  Adjunction.rightAdjointUniq
    (adj.ofNatIsoLeft e)
    (Adjunction.id (C := DerivedCategory (ModuleCat A)))

/-- 0E1U: The objectwise canonical comparison `RHom_A(A[0], K) ≅ K`. -/
@[stacks 0E1U "canonical RHom unit object from explicit comparison"]
noncomputable abbrev objIsoOf
    (adj : DerivedTensor.Right.functor (single (A := A)) ⊣
      RHom.targetFunctor (A := A) (single (A := A)))
    (e : DerivedTensor.Right.functor (single (A := A)) ≅
      𝟭 (DerivedCategory (ModuleCat A)))
    (K : DerivedCategory (ModuleCat A)) :
    RHom.obj (A := A) (single (A := A)) K ≅ K :=
  (targetIsoOf (A := A) adj e).app K

/-- 0E1U: The canonical `RHom(A[0], -)` unit comparison is natural in its target. -/
@[reassoc, stacks 0E1U "canonical RHom unit naturality"]
theorem objIsoOf_naturality
    (adj : DerivedTensor.Right.functor (single (A := A)) ⊣
      RHom.targetFunctor (A := A) (single (A := A)))
    (e : DerivedTensor.Right.functor (single (A := A)) ≅
      𝟭 (DerivedCategory (ModuleCat A)))
    {K L : DerivedCategory (ModuleCat A)} (f : K ⟶ L) :
    (RHom.targetFunctor (A := A) (single (A := A))).map f ≫
        (objIsoOf (A := A) adj e L).hom =
      (objIsoOf (A := A) adj e K).hom ≫ f := by
  simpa using (targetIsoOf (A := A) adj e).hom.naturality f

/-- 0E1U: Under the unit comparison, regular-source precomposition becomes scalar multiplication on
the target object. -/
@[reassoc, stacks 0E1U "regular RHom scalar comparison"]
theorem singlePre_objIsoOf_hom
    (adj : DerivedTensor.Right.functor (single (A := A)) ⊣
      RHom.targetFunctor (A := A) (single (A := A)))
    (e : DerivedTensor.Right.functor (single (A := A)) ≅
      𝟭 (DerivedCategory (ModuleCat A)))
    (a : A) (K : DerivedCategory (ModuleCat A)) :
    (singlePre (A := A) a).app K ≫ (objIsoOf (A := A) adj e K).hom =
      (objIsoOf (A := A) adj e K).hom ≫ (a • 𝟙 K) := by
  rw [singlePre_app_eq_smul]
  simp

end RHom

end CategoryTheory.DerivedCategory.InternalHom.RHom.Unit
