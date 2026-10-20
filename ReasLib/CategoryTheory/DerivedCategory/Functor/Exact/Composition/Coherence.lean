/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Identity
public import ReasLib.CategoryTheory.Functor.Exactness.Composition.Coherence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Coherence of exact functors on derived categories

The canonical identity and composition comparisons for passage to derived
categories satisfy the associativity and unit laws of a pseudofunctor.  The
laws are stated as equalities of natural isomorphisms, so downstream code can
use them at the functor level or evaluate them on any object.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w₁ w₂ w₃ w₄ v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.ExactFunctor.MapDerivedCategory

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
variable {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]
variable {D : Type u₄} [Category.{v₄} D] [Abelian D] [HasDerivedCategory.{w₄} D]

namespace compFunctorIso

/-- The exact-derived composition comparison satisfies the associativity
coherence law. -/
@[stacks 015F "associativity coherence for exact derived functors"]
theorem associativity (F : A ⥤ₑ B) (G : B ⥤ₑ C) (H : C ⥤ₑ D) :
    compFunctorIso (F.comp G) H ≪≫
        Functor.isoWhiskerRight (compFunctorIso F G) H.mapDerivedCategory ≪≫
        Functor.associator F.mapDerivedCategory G.mapDerivedCategory
          H.mapDerivedCategory =
      mapIso (ExactFunctor.associator F G H) ≪≫
        compFunctorIso F (G.comp H) ≪≫
        Functor.isoWhiskerLeft F.mapDerivedCategory (compFunctorIso G H) := sorry

/-- The exact-derived identity and composition comparisons satisfy the left
unit coherence law. -/
@[stacks 015F "left unit coherence for exact derived functors"]
theorem left_unit (F : A ⥤ₑ B) :
    compFunctorIso (ExactFunctor.id A) F ≪≫
        Functor.isoWhiskerRight (idFunctorIso A) F.mapDerivedCategory ≪≫
        Functor.leftUnitor F.mapDerivedCategory =
      mapIso (ExactFunctor.leftUnitor F) := sorry

/-- The exact-derived identity and composition comparisons satisfy the right
unit coherence law. -/
@[stacks 015F "right unit coherence for exact derived functors"]
theorem right_unit (F : A ⥤ₑ B) :
    compFunctorIso F (ExactFunctor.id B) ≪≫
        Functor.isoWhiskerLeft F.mapDerivedCategory (idFunctorIso B) ≪≫
        Functor.rightUnitor F.mapDerivedCategory =
      mapIso (ExactFunctor.rightUnitor F) := sorry

end compFunctorIso

end CategoryTheory.ExactFunctor.MapDerivedCategory
