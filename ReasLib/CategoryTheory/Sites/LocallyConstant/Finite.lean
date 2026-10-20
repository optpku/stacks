/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.LocallyConstant.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Finite locally constant sheaves

This leaf specializes `Sheaf.IsLocallyConstantWith` to finite sets, finite
groups, finite abelian groups, and finite-type modules.
-/

@[expose] public section

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace Sheaf

section FiniteLocallyConstantTypes

variable [HasWeakSheafify J (Type w)]
variable [∀ U : C, HasWeakSheafify (J.over U) (Type w)]

/-- A set-valued sheaf is finite locally constant when its local constant models have
finite values. -/
abbrev IsFiniteLocallyConstant (F : Sheaf J (Type w)) : Prop :=
  IsLocallyConstantWith (J := J) Finite F

namespace IsFiniteLocallyConstant

/-- The finite constant charts supplied by a finite locally constant set-valued sheaf. -/
theorem existsFiniteConstantCover (F : Sheaf J (Type w)) [IsFiniteLocallyConstant F]
    (U : C) :
    ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
      ∀ i : I, ∃ E : Type w, Finite E ∧
        Nonempty (F.over (X i).left ≅ (constantSheaf (J.over (X i).left) (Type w)).obj E) := sorry

end IsFiniteLocallyConstant

/-- The object property of finite locally constant set-valued sheaves. -/
abbrev finiteLocallyConstant (J : GrothendieckTopology C) [HasWeakSheafify J (Type w)]
    [∀ U : C, HasWeakSheafify (J.over U) (Type w)] : ObjectProperty (Sheaf J (Type w)) :=
  fun F ↦ IsFiniteLocallyConstant F

/-- A finite locally constant sheaf of sets is locally constant. -/
instance IsFiniteLocallyConstant.toIsLocallyConstant (F : Sheaf J (Type w))
    [IsFiniteLocallyConstant F] : IsLocallyConstant F := sorry

/-- A constant sheaf with finite set value is finite locally constant. -/
instance IsFiniteLocallyConstant.ofConstant (E : Type w) [Finite E]
    [J.WEqualsLocallyBijective (Type w)]
    [∀ U : C, (J.over U).WEqualsLocallyBijective (Type w)] :
    IsFiniteLocallyConstant ((constantSheaf J (Type w)).obj E) := sorry

end FiniteLocallyConstantTypes

section FiniteLocallyConstantGroups

variable [HasWeakSheafify J GrpCat.{w}]
variable [∀ U : C, HasWeakSheafify (J.over U) GrpCat.{w}]

/-- A group-valued sheaf is finite locally constant when its local constant models have
finite group values. -/
abbrev IsFiniteLocallyConstantGrp (F : Sheaf J GrpCat.{w}) : Prop :=
  IsLocallyConstantWith (J := J) (fun A : GrpCat.{w} ↦ Finite A) F

namespace IsFiniteLocallyConstantGrp

/-- The finite constant group charts supplied by a finite locally constant group-valued sheaf. -/
theorem existsFiniteConstantCover (F : Sheaf J GrpCat.{w}) [IsFiniteLocallyConstantGrp F]
    (U : C) :
    ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
      ∀ i : I, ∃ A : GrpCat.{w}, Finite A ∧
        Nonempty (F.over (X i).left ≅ (constantSheaf (J.over (X i).left) GrpCat.{w}).obj A) := sorry

end IsFiniteLocallyConstantGrp

/-- The object property of finite locally constant group-valued sheaves. -/
abbrev finiteLocallyConstantGrp (J : GrothendieckTopology C) [HasWeakSheafify J GrpCat.{w}]
    [∀ U : C, HasWeakSheafify (J.over U) GrpCat.{w}] : ObjectProperty (Sheaf J GrpCat.{w}) :=
  fun F ↦ IsFiniteLocallyConstantGrp F

/-- A finite locally constant sheaf of groups is locally constant. -/
instance IsFiniteLocallyConstantGrp.toIsLocallyConstant
    (F : Sheaf J GrpCat.{w}) [IsFiniteLocallyConstantGrp F] :
    IsLocallyConstant F := sorry

/-- A constant sheaf with finite group value is finite locally constant. -/
instance IsFiniteLocallyConstantGrp.ofConstant (A : GrpCat.{w}) [Finite A]
    [J.WEqualsLocallyBijective GrpCat.{w}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective GrpCat.{w}] :
    IsFiniteLocallyConstantGrp ((constantSheaf J GrpCat.{w}).obj A) := sorry

end FiniteLocallyConstantGroups

section FiniteLocallyConstantAddCommGroups

variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]

/-- A sheaf of abelian groups is finite locally constant when its local constant models have
finite abelian-group values. -/
abbrev IsFiniteLocallyConstantAddCommGrp (F : Sheaf J AddCommGrpCat.{w}) : Prop :=
  IsLocallyConstantWith (J := J) (fun A : AddCommGrpCat.{w} ↦ Finite A) F

namespace IsFiniteLocallyConstantAddCommGrp

/-- The finite constant abelian-group charts supplied by a finite locally constant sheaf. -/
theorem existsFiniteConstantCover
    (F : Sheaf J AddCommGrpCat.{w}) [IsFiniteLocallyConstantAddCommGrp F] (U : C) :
    ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
      ∀ i : I, ∃ A : AddCommGrpCat.{w}, Finite A ∧
        Nonempty (F.over (X i).left ≅
          (constantSheaf (J.over (X i).left) AddCommGrpCat.{w}).obj A) := sorry

end IsFiniteLocallyConstantAddCommGrp

/-- The object property of finite locally constant abelian-group-valued sheaves. -/
abbrev finiteLocallyConstantAddCommGrp (J : GrothendieckTopology C)
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}] :
    ObjectProperty (Sheaf J AddCommGrpCat.{w}) :=
  fun F ↦ IsFiniteLocallyConstantAddCommGrp F

/-- A finite locally constant sheaf of abelian groups is locally constant. -/
instance IsFiniteLocallyConstantAddCommGrp.toIsLocallyConstant
    (F : Sheaf J AddCommGrpCat.{w}) [IsFiniteLocallyConstantAddCommGrp F] :
    IsLocallyConstant F := sorry

/-- A constant sheaf with finite abelian-group value is finite locally constant. -/
instance IsFiniteLocallyConstantAddCommGrp.ofConstant
    (A : AddCommGrpCat.{w}) [Finite A]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}] :
    IsFiniteLocallyConstantAddCommGrp ((constantSheaf J AddCommGrpCat.{w}).obj A) := sorry

end FiniteLocallyConstantAddCommGroups

section FiniteTypeLocallyConstantModules

variable {Λ : Type w} [Ring Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]

/-- A module-valued sheaf is locally constant of finite type when its local constant models are
finite `Λ`-modules. -/
abbrev IsFiniteTypeLocallyConstantModule (F : Sheaf J (ModuleCat.{w} Λ)) : Prop :=
  IsLocallyConstantWith (J := J) (fun M : ModuleCat.{w} Λ ↦ Module.Finite Λ M) F

namespace IsFiniteTypeLocallyConstantModule

/-- The finite-type constant module charts supplied by a locally constant sheaf of finite type. -/
theorem existsFiniteConstantCover
    (F : Sheaf J (ModuleCat.{w} Λ)) [IsFiniteTypeLocallyConstantModule F] (U : C) :
    ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
      ∀ i : I, ∃ M : ModuleCat.{w} Λ, Module.Finite Λ M ∧
        Nonempty (F.over (X i).left ≅
          (constantSheaf (J.over (X i).left) (ModuleCat.{w} Λ)).obj M) := sorry

end IsFiniteTypeLocallyConstantModule

/-- The object property of locally constant sheaves of finite `Λ`-modules. -/
abbrev finiteTypeLocallyConstantModule (J : GrothendieckTopology C) (Λ : Type w) [Ring Λ]
    [HasWeakSheafify J (ModuleCat.{w} Λ)]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)] :
    ObjectProperty (Sheaf J (ModuleCat.{w} Λ)) :=
  fun F ↦ IsFiniteTypeLocallyConstantModule F

/-- A locally constant sheaf of finite-type modules is locally constant. -/
instance IsFiniteTypeLocallyConstantModule.toIsLocallyConstant
    (F : Sheaf J (ModuleCat.{w} Λ)) [IsFiniteTypeLocallyConstantModule F] :
    IsLocallyConstant F := sorry

/-- A constant sheaf with finite `Λ`-module value is locally constant of finite type. -/
instance IsFiniteTypeLocallyConstantModule.ofConstant
    (M : ModuleCat.{w} Λ) [Module.Finite Λ M]
    [J.WEqualsLocallyBijective (ModuleCat.{w} Λ)]
    [∀ U : C, (J.over U).WEqualsLocallyBijective (ModuleCat.{w} Λ)] :
    IsFiniteTypeLocallyConstantModule ((constantSheaf J (ModuleCat.{w} Λ)).obj M) := sorry

end FiniteTypeLocallyConstantModules

end Sheaf

end CategoryTheory
