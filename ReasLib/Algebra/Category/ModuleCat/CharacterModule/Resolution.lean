/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.CharacterModule.Evaluation
public import ReasLib.Algebra.Category.ModuleCat.CharacterModule.Functor.MonoEpi
public import ReasLib.Algebra.Category.ModuleCat.Free.Adjunction
public import ReasLib.CategoryTheory.Abelian.FunctorialInjectives.Definition
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Functorial injective embeddings from character modules

For a left module `M` over an arbitrary ring `R`, this file implements the
source construction `J(M) = CharacterModule (F (CharacterModule M))` with
`F` taken over `Rᵐᵒᵖ`. The second character dual is transported along
`RingEquiv.opOp R`; evaluation followed by dualization of the free-module
counit gives a natural embedding `M ⟶ J(M)`.

@stack 01DC
@stack 01DD
-/

open CategoryTheory

noncomputable section

universe u v

namespace CharacterModule.Resolution

variable (R : Type u) [Ring R]

/-- The endofunctor `M ↦ CharacterModule (F (CharacterModule M))` for an
arbitrary ring.  The free module is formed over `Rᵐᵒᵖ`, where the first
character dual naturally lives. -/
@[stacks 01DD "character-module injective-target functor"]
noncomputable abbrev functor :
    ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} R :=
  (CharacterModule.opFunctor R).rightOp ⋙
    (CategoryTheory.forget (ModuleCat.{max u v} Rᵐᵒᵖ) ⋙
      ModuleCat.Free.functor.{u, v} Rᵐᵒᵖ).op ⋙
      CharacterModule.opFunctor Rᵐᵒᵖ ⋙
      ModuleCat.restrictScalars (RingEquiv.opOp R).toRingHom

/-- The free module over `Rᵐᵒᵖ` on the underlying set of the character
module of `M`. -/
@[stacks 01DD "free opposite-ring module in the character resolution"]
noncomputable abbrev freeObj (M : ModuleCat.{max u v} R) :
    ModuleCat.{max u v} Rᵐᵒᵖ :=
  ModuleCat.Free.obj Rᵐᵒᵖ (CharacterModule M)

/-- The canonical injective target `J(M) = CharacterModule (F
(CharacterModule M))`, with the second character dual transported from
`Rᵐᵒᵖᵐᵒᵖ` to `R`. -/
@[stacks 01DC "explicit character-module injective target"]
noncomputable abbrev obj (M : ModuleCat.{max u v} R) :
    ModuleCat.{max u v} R :=
  ModuleCat.of R (CharacterModule (freeObj R M))

/-- The objectwise form of the character-module resolution functor is the
explicit module `J(M)`. -/
@[simp]
theorem functor_obj (M : ModuleCat.{max u v} R) :
    (functor R).obj M = obj R M := rfl

/-- The explicit value of the embedding at an element of `M`, as a
character on the free `Rᵐᵒᵖ`-module. -/
@[stacks 01DD "pointwise character-module embedding value"]
def ιAppValue (M : ModuleCat.{max u v} R) :
    M →+ CharacterModule (freeObj R M) :=
  ((CharacterModule.dualOpposite
      ((ModuleCat.Free.counit.{u, v} Rᵐᵒᵖ).app
        ((CharacterModule.opFunctor R).obj (Opposite.op M))).hom).toAddMonoidHom).comp
    (CharacterModule.eval : M →+ CharacterModule (CharacterModule M))

/-- The underlying additive embedding into the character-module target. -/
@[stacks 01DD "additive character-module embedding"]
def ιAppAdd (M : ModuleCat.{max u v} R) :
    (forget₂ (ModuleCat R) AddCommGrpCat).obj M ⟶
      (forget₂ (ModuleCat R) AddCommGrpCat).obj (obj R M) :=
  AddCommGrpCat.ofHom (ιAppValue R M)

/-- The explicit additive embedding commutes with the `R`-actions. -/
theorem ιApp_smul_naturality (M : ModuleCat.{max u v} R) (r : R) :
    ιAppAdd R M ≫ (obj R M).smul r = M.smul r ≫ ιAppAdd R M := by
  ext m
  apply CharacterModule.ext
  intro z
  let ε : freeObj R M ⟶ CharacterModule.oppositeObj R M :=
    (ModuleCat.Free.counit.{u, v} Rᵐᵒᵖ).app
      ((CharacterModule.opFunctor R).obj (Opposite.op M))
  change (ε.hom (MulOpposite.op r • z) : CharacterModule M) m =
    (ε.hom z : CharacterModule M) (r • (show M from m))
  rw [ε.hom.map_smul]
  rfl

/-- The bundled map from `M` into its character-module injective target. -/
@[stacks 01DD "canonical map into the character-module injective target"]
noncomputable def ιApp (M : ModuleCat.{max u v} R) : M ⟶ obj R M :=
  ModuleCat.homMk (ιAppAdd R M) (ιApp_smul_naturality R M)

/-- The canonical maps `M ⟶ J(M)` are natural in `M`. -/
theorem ι_naturality {M N : ModuleCat.{max u v} R} (f : M ⟶ N) :
    f ≫ ιApp R N = ιApp R M ≫ (functor R).map f := by
  ext m z
  have h := congr_arg (fun g : freeObj R N ⟶ CharacterModule.oppositeObj R M => g z m)
    ((ModuleCat.Free.counit.{u, v} Rᵐᵒᵖ).naturality
      (CharacterModule.dualOppositeMap R f))
  exact h.symm

/-- The canonical embeddings assemble into a natural transformation. -/
@[stacks 01DD "functorial character-module embedding"]
noncomputable def ι : 𝟭 (ModuleCat.{max u v} R) ⟶ functor R where
  app := ιApp R
  naturality := fun {_ _} f ↦ ι_naturality R f

/-- The source construction as a functor to the arrow category. -/
@[stacks 01DD "functor of character-module injective embeddings"]
noncomputable abbrev arrowFunctor :
    ModuleCat.{max u v} R ⥤ Arrow (ModuleCat.{max u v} R) :=
  (ι R).arrowFunctor

/-- The canonical embedding is evaluation on the free `Rᵐᵒᵖ`-generators of
`F(CharacterModule M)`. -/
@[simp]
theorem ιAppValue_freeMk (M : ModuleCat.{max u v} R) (m : M)
    (χ : CharacterModule M) :
    ιAppValue R M m (ModuleCat.Free.mk Rᵐᵒᵖ χ) = χ m := by
  change CharacterModule.eval m
      ((ModuleCat.Free.counit.{u, v} Rᵐᵒᵖ).app
        ((CharacterModule.opFunctor R).obj (Opposite.op M))
        (ModuleCat.Free.mk Rᵐᵒᵖ χ)) = χ m
  rw [ModuleCat.Free.counit_mk]
  exact CharacterModule.eval_apply m χ

/-- Every canonical map `M ⟶ J(M)` is injective on elements. -/
theorem ιApp_injective (M : ModuleCat.{max u v} R) :
    Function.Injective (ιApp R M) := by
  intro m n h
  apply sub_eq_zero.mp
  apply CharacterModule.eq_zero_of_character_apply
  intro χ
  rw [map_sub]
  apply sub_eq_zero.mpr
  have hχ := congr_arg (fun x => x (ModuleCat.Free.mk Rᵐᵒᵖ χ)) h
  change ιAppValue R M m (ModuleCat.Free.mk Rᵐᵒᵖ χ) =
    ιAppValue R M n (ModuleCat.Free.mk Rᵐᵒᵖ χ) at hχ
  exact (ιAppValue_freeMk R M m χ).symm.trans (hχ.trans (ιAppValue_freeMk R M n χ))

/-- Every canonical map `M ⟶ J(M)` is a monomorphism. -/
@[stacks 01DC "character-module embedding is monic"]
instance mono_ιApp (M : ModuleCat.{max u v} R) : Mono (ιApp R M) :=
  (ModuleCat.mono_iff_injective _).mpr (ιApp_injective R M)

/-- Lemma 15.55.8, tag `01DC`: the explicit module `J(M)` is injective. -/
@[stacks 01DC "injectivity of the character-module target"]
theorem injective (M : ModuleCat.{max u v} R) :
    Module.Injective R (obj R M) := by
  classical
  refine ⟨fun X Y _ _ _ _ f hf g => ?_⟩
  -- First extend the values on the unit generators to a divisible abelian group.
  let g₀ : X →+ (CharacterModule M → AddCircle (1 : ℚ)) :=
    { toFun := fun x χ => g x (Finsupp.single χ (1 : Rᵐᵒᵖ))
      map_zero' := by
        ext χ
        change (g (0 : X)) (Finsupp.single χ (1 : Rᵐᵒᵖ)) = 0
        rw [map_zero]
        rfl
      map_add' := by
        intro x x'
        ext χ
        change (g (x + x')) (Finsupp.single χ (1 : Rᵐᵒᵖ)) = _
        rw [map_add]
        rfl }
  obtain ⟨h, hh⟩ :=
    (Module.Baer.of_divisible (CharacterModule M → AddCircle (1 : ℚ))).extension_property_addMonoidHom
      f.toAddMonoidHom hf g₀
  -- Recover an R-linear extension using the opposite-ring coefficients of the free module.
  let c (y : Y) : CharacterModule (freeObj R M) :=
    Finsupp.liftAddHom fun χ =>
      { toFun := fun a : Rᵐᵒᵖ => h (MulOpposite.unop a • y) χ
        map_zero' := by
          simp only [MulOpposite.unop_zero, zero_smul, map_zero]
          rfl
        map_add' := by
          intro a b
          rw [MulOpposite.unop_add, add_smul, map_add]
          rfl }
  have hc (y : Y) (χ : CharacterModule M) (a : Rᵐᵒᵖ) :
      c y (Finsupp.single χ a) = h (MulOpposite.unop a • y) χ :=
    Finsupp.liftAddHom_apply_single _ _ _
  let k : Y →ₗ[R] obj R M :=
    { toFun := c
      map_add' := by
        intro y y'
        apply Finsupp.addHom_ext
        intro χ a
        change c (y + y') (Finsupp.single χ a) =
          c y (Finsupp.single χ a) + c y' (Finsupp.single χ a)
        rw [hc, hc, hc, smul_add, map_add]
        rfl
      map_smul' := by
        intro r y
        apply Finsupp.addHom_ext
        intro χ a
        change c (r • y) (Finsupp.single χ a) =
          c y (MulOpposite.op r • Finsupp.single χ a)
        rw [Finsupp.smul_single, hc, hc]
        simp only [smul_eq_mul, MulOpposite.unop_mul, MulOpposite.unop_op, mul_smul] }
  refine ⟨k, fun x => ?_⟩
  apply Finsupp.addHom_ext
  intro χ a
  change c (f x) (Finsupp.single χ a) = g x (Finsupp.single χ a)
  rw [hc, ← f.map_smul]
  have hx := congr_arg (fun q : X →+ (CharacterModule M → AddCircle (1 : ℚ)) =>
    q (MulOpposite.unop a • x) χ) hh
  change h (f (MulOpposite.unop a • x)) χ = g (MulOpposite.unop a • x) (Finsupp.single χ 1) at hx
  rw [hx, g.map_smul]
  change g x (MulOpposite.op (MulOpposite.unop a) • Finsupp.single χ 1) = _
  simp [Finsupp.smul_single]

/-- The categorical form of injectivity of `J(M)`. -/
@[stacks 01DC "character-module target is injective"]
instance obj_injective (M : ModuleCat.{max u v} R) :
    Injective (obj R M) := by
  apply (Module.injective_iff_injective_object R (obj R M)).mp
  exact injective R M

/-- The explicit target and embedding give an injective presentation of
`M`. -/
@[stacks 01DD "explicit character-module injective presentation"]
noncomputable def presentation (M : ModuleCat.{max u v} R) :
    InjectivePresentation M where
  J := obj R M
  injective := obj_injective R M
  f := ιApp R M
  mono := mono_ιApp R M

/-- Lemma 15.55.9, tag `01DD`: the explicit character-module construction
supplies functorial injective embeddings. This is a named value rather than a
global instance, so consumers can choose it without changing ambient instance
search. -/
@[stacks 01DD "character-module functorial injective embeddings", reducible]
noncomputable def functorialInjectives :
    HasFunctorialInjectives (ModuleCat.{max u v} R) where
  functor := functor R
  ι := ι R
  mono_app := mono_ιApp R
  injective_obj := obj_injective R

end CharacterModule.Resolution
