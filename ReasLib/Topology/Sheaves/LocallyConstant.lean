/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.LocallyConstant.Algebra

/-!
# The abelian sheaf of locally constant functions

For a topological space `X` and an abelian group `A`, the sections of
`TopologicalSpace.locallyConstantSheaf X A` over an open `U` are the locally constant
functions `U → A`, with restriction given by precomposition with the inclusion of opens.
This is the standard concrete model of the constant sheaf `A` on `X`.

## Main declarations

- `TopologicalSpace.locallyConstantRestrict`: restriction of locally constant functions
- `TopologicalSpace.locallyConstantSheaf`: the abelian sheaf of locally constant functions
- `TopologicalSpace.constantSheafToLocallyConstantSheaf`: the map from the constant sheaf
  adjoint to the global constant functions
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u v

namespace TopologicalSpace

section Presheaf

variable {X : Type u} [TopologicalSpace X] (A : Type v) [AddCommGroup A]

/-- Restriction of locally constant functions along an inclusion of opens `V ≤ U`. -/
def locallyConstantRestrict {U V : Opens X} (hVU : V ≤ U) :
    LocallyConstant U A →+ LocallyConstant V A :=
  LocallyConstant.comapAddMonoidHom (ContinuousMap.inclusion hVU)

/-- Restriction of locally constant functions evaluates at the included point. -/
@[simp]
theorem locallyConstantRestrict_apply {U V : Opens X} (hVU : V ≤ U)
    (f : LocallyConstant U A) (x : V) :
    locallyConstantRestrict A hVU f x = f (Set.inclusion hVU x) := rfl

variable (X)

/-- The presheaf of abelian groups of locally constant `A`-valued functions on opens of `X`. -/
def locallyConstantPresheaf : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{max u v} where
  obj U := AddCommGrpCat.of (LocallyConstant U.unop A)
  map i := AddCommGrpCat.ofHom (locallyConstantRestrict A i.unop.le)
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- Locally constant functions satisfy the sheaf condition for open covers. -/
theorem isSheaf_locallyConstantPresheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (locallyConstantPresheaf X A) := sorry

/-- The abelian sheaf of locally constant `A`-valued functions on `X`. -/
def locallyConstantSheaf : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v} :=
  ⟨locallyConstantPresheaf X A, isSheaf_locallyConstantPresheaf X A⟩

/-- Sections of the locally constant sheaf over `U` are locally constant functions on `U`. -/
theorem locallyConstantSheaf_obj_obj (U : (Opens X)ᵒᵖ) :
    (locallyConstantSheaf X A).obj.obj U = AddCommGrpCat.of (LocallyConstant U.unop A) := rfl

end Presheaf

section Comparison

variable (X : Type u) [TopologicalSpace X] (A : Type v) [AddCommGroup A]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]

/-- The morphism from the constant sheaf on `B` to the locally constant `A`-valued sheaf which
is adjoint to `b ↦ const (φ b)` on global sections. For a bijective `φ` this is the
identification of the constant sheaf with the sheaf of locally constant functions. -/
noncomputable def constantSheafToLocallyConstantSheaf {B : Type (max u v)} [AddCommGroup B]
    (φ : B →+ A) :
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).obj
        (AddCommGrpCat.of B) ⟶ locallyConstantSheaf X A :=
  ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}
      (Limits.isTerminalTop (α := Opens X))).homEquiv _ _).symm
    (AddCommGrpCat.ofHom
      ((LocallyConstant.constAddMonoidHom : A →+ LocallyConstant (⊤ : Opens X) A).comp φ))

/-- On global sections, `constantSheafToLocallyConstantSheaf φ` corresponds under the
constant-sheaf adjunction to `b ↦ const (φ b)`. -/
theorem constantSheafAdj_homEquiv_constantSheafToLocallyConstantSheaf
    {B : Type (max u v)} [AddCommGroup B] (φ : B →+ A) :
    (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}
        (Limits.isTerminalTop (α := Opens X))).homEquiv _ _
        (constantSheafToLocallyConstantSheaf X A φ) =
      AddCommGrpCat.ofHom
        ((LocallyConstant.constAddMonoidHom : A →+ LocallyConstant (⊤ : Opens X) A).comp φ) :=
  Equiv.apply_symm_apply _ _

/-- For a bijective `φ`, the comparison from the constant sheaf to the sheaf of locally
constant functions is an isomorphism. -/
theorem isIso_constantSheafToLocallyConstantSheaf {B : Type (max u v)} [AddCommGroup B]
    {φ : B →+ A} (hφ : Function.Bijective φ) :
    IsIso (constantSheafToLocallyConstantSheaf X A φ) := sorry

end Comparison

end TopologicalSpace
