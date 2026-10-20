module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Composition.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Identity
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition.Coherence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Coherence of bounded exact-derived functors

The identity and composition comparisons for exact functors on the
bounded-below, bounded-above, and bounded derived categories satisfy the
pseudofunctor associativity and unit laws.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w₁ w₂ w₃ w₄ v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.ExactFunctor.Derived

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
variable {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]
variable {D : Type u₄} [Category.{v₄} D] [Abelian D] [HasDerivedCategory.{w₄} D]

namespace Plus.compFunctorIso

/-- The bounded-below exact-derived composition comparison satisfies the
associativity coherence law. -/
@[stacks 015F "bounded-below exact-derived associativity coherence"]
theorem associativity (F : A ⥤ₑ B) (G : B ⥤ₑ C) (H : C ⥤ₑ D) :
    Plus.compFunctorIso (F.comp G) H ≪≫
        Functor.isoWhiskerRight (Plus.compFunctorIso F G) (Plus.functor H) ≪≫
        Functor.associator (Plus.functor F) (Plus.functor G) (Plus.functor H) =
      Plus.mapIso (ExactFunctor.associator F G H) ≪≫
        Plus.compFunctorIso F (G.comp H) ≪≫
        Functor.isoWhiskerLeft (Plus.functor F) (Plus.compFunctorIso G H) := sorry

/-- The bounded-below exact-derived comparisons satisfy the left unit
coherence law. -/
@[stacks 015F "bounded-below exact-derived left unit coherence"]
theorem left_unit (F : A ⥤ₑ B) :
    Plus.compFunctorIso (ExactFunctor.id A) F ≪≫
        Functor.isoWhiskerRight (Plus.idFunctorIso A) (Plus.functor F) ≪≫
        Functor.leftUnitor (Plus.functor F) =
      Plus.mapIso (ExactFunctor.leftUnitor F) := sorry

/-- The bounded-below exact-derived comparisons satisfy the right unit
coherence law. -/
@[stacks 015F "bounded-below exact-derived right unit coherence"]
theorem right_unit (F : A ⥤ₑ B) :
    Plus.compFunctorIso F (ExactFunctor.id B) ≪≫
        Functor.isoWhiskerLeft (Plus.functor F) (Plus.idFunctorIso B) ≪≫
        Functor.rightUnitor (Plus.functor F) =
      Plus.mapIso (ExactFunctor.rightUnitor F) := sorry

end Plus.compFunctorIso

namespace Minus.compFunctorIso

/-- The bounded-above exact-derived composition comparison satisfies the
associativity coherence law. -/
@[stacks 015F "bounded-above exact-derived associativity coherence"]
theorem associativity (F : A ⥤ₑ B) (G : B ⥤ₑ C) (H : C ⥤ₑ D) :
    Minus.compFunctorIso (F.comp G) H ≪≫
        Functor.isoWhiskerRight (Minus.compFunctorIso F G) (Minus.functor H) ≪≫
        Functor.associator (Minus.functor F) (Minus.functor G) (Minus.functor H) =
      Minus.mapIso (ExactFunctor.associator F G H) ≪≫
        Minus.compFunctorIso F (G.comp H) ≪≫
        Functor.isoWhiskerLeft (Minus.functor F) (Minus.compFunctorIso G H) := sorry

/-- The bounded-above exact-derived comparisons satisfy the left unit
coherence law. -/
@[stacks 015F "bounded-above exact-derived left unit coherence"]
theorem left_unit (F : A ⥤ₑ B) :
    Minus.compFunctorIso (ExactFunctor.id A) F ≪≫
        Functor.isoWhiskerRight (Minus.idFunctorIso A) (Minus.functor F) ≪≫
        Functor.leftUnitor (Minus.functor F) =
      Minus.mapIso (ExactFunctor.leftUnitor F) := sorry

/-- The bounded-above exact-derived comparisons satisfy the right unit
coherence law. -/
@[stacks 015F "bounded-above exact-derived right unit coherence"]
theorem right_unit (F : A ⥤ₑ B) :
    Minus.compFunctorIso F (ExactFunctor.id B) ≪≫
        Functor.isoWhiskerLeft (Minus.functor F) (Minus.idFunctorIso B) ≪≫
        Functor.rightUnitor (Minus.functor F) =
      Minus.mapIso (ExactFunctor.rightUnitor F) := sorry

end Minus.compFunctorIso

namespace Bounded.compFunctorIso

/-- The bounded exact-derived composition comparison satisfies the
associativity coherence law. -/
@[stacks 015F "bounded exact-derived associativity coherence"]
theorem associativity (F : A ⥤ₑ B) (G : B ⥤ₑ C) (H : C ⥤ₑ D) :
    Bounded.compFunctorIso (F.comp G) H ≪≫
        Functor.isoWhiskerRight (Bounded.compFunctorIso F G) (Bounded.functor H) ≪≫
        Functor.associator (Bounded.functor F) (Bounded.functor G)
          (Bounded.functor H) =
      Bounded.mapIso (ExactFunctor.associator F G H) ≪≫
        Bounded.compFunctorIso F (G.comp H) ≪≫
        Functor.isoWhiskerLeft (Bounded.functor F)
          (Bounded.compFunctorIso G H) := sorry

/-- The bounded exact-derived comparisons satisfy the left unit coherence
law. -/
@[stacks 015F "bounded exact-derived left unit coherence"]
theorem left_unit (F : A ⥤ₑ B) :
    Bounded.compFunctorIso (ExactFunctor.id A) F ≪≫
        Functor.isoWhiskerRight (Bounded.idFunctorIso A) (Bounded.functor F) ≪≫
        Functor.leftUnitor (Bounded.functor F) =
      Bounded.mapIso (ExactFunctor.leftUnitor F) := sorry

/-- The bounded exact-derived comparisons satisfy the right unit coherence
law. -/
@[stacks 015F "bounded exact-derived right unit coherence"]
theorem right_unit (F : A ⥤ₑ B) :
    Bounded.compFunctorIso F (ExactFunctor.id B) ≪≫
        Functor.isoWhiskerLeft (Bounded.functor F) (Bounded.idFunctorIso B) ≪≫
        Functor.rightUnitor (Bounded.functor F) =
      Bounded.mapIso (ExactFunctor.rightUnitor F) := sorry

end Bounded.compFunctorIso

end CategoryTheory.ExactFunctor.Derived
