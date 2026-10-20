/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Locally constant sheaves with finitely presented module models

The local constant models of a module-valued sheaf may be required to be finitely
presented over the coefficient ring.
-/

@[expose] public section

universe u v w

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [Ring Λ]

namespace LocallyConstant

variable [HasWeakSheafify J (ModuleCat.{max u v w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]

/-- A module-valued sheaf has finitely presented local constant models when every slice
site admits a covering on which it is constant with finitely presented module values. -/
@[stacks 093T "finite-presentation constant models"]
abbrev IsFinitePresentation
    (F : Sheaf J (ModuleCat.{max u v w} Λ)) : Prop :=
  IsLocallyConstantWith (J := J)
    (fun M : ModuleCat.{max u v w} Λ ↦ Module.FinitePresentation Λ M) F

/-- The object property selecting locally constant module sheaves with finitely presented
constant models. -/
abbrev finitePresentation :
    ObjectProperty (Sheaf J (ModuleCat.{max u v w} Λ)) :=
  fun F ↦ IsFinitePresentation F

namespace IsFinitePresentation

/-- The finitely presented constant charts supplied by a locally constant module sheaf of finite
presentation. -/
theorem existsConstantCover
    (F : Sheaf J (ModuleCat.{max u v w} Λ)) [IsFinitePresentation F] (U : C) :
    ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
      ∀ i : I, ∃ M : ModuleCat.{max u v w} Λ, Module.FinitePresentation Λ M ∧
        Nonempty (F.over (X i).left ≅
          (constantSheaf (J.over (X i).left) (ModuleCat.{max u v w} Λ)).obj M) := sorry

/-- Forgetting finite presentation of the constant models leaves ordinary local constancy. -/
instance toIsLocallyConstant
    (F : Sheaf J (ModuleCat.{max u v w} Λ)) [IsFinitePresentation F] :
    IsLocallyConstant F := sorry

/-- Local finite presentation by constant models is invariant under sheaf isomorphism. -/
theorem of_iso {F G : Sheaf J (ModuleCat.{max u v w} Λ)}
    (e : F ≅ G) [IsFinitePresentation F] :
    IsFinitePresentation G := sorry

/-- A constant sheaf on a finitely presented module has finitely presented constant models. -/
@[stacks 093T "finitely presented constant sheaf"]
instance ofConstant
    (M : ModuleCat.{max u v w} Λ) [Module.FinitePresentation Λ M]
    [J.WEqualsLocallyBijective (ModuleCat.{max u v w} Λ)]
    [∀ U : C, (J.over U).WEqualsLocallyBijective (ModuleCat.{max u v w} Λ)] :
    IsFinitePresentation ((constantSheaf J (ModuleCat.{max u v w} Λ)).obj M) := sorry

end IsFinitePresentation

end LocallyConstant

end CategoryTheory.Sheaf
