/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Degree.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition.BoundedBelow.Exact
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Homology
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.RightDerived
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded right-derived degrees after an exact functor

An exact second functor does not contribute higher right-derived information.  This file packages
that principle first at the bounded-below derived-functor level and then degreewise.  The degree
comparison is assembled from the canonical composition comparison and the canonical homology
comparison for an exact functor; it does not choose an isomorphism from an `IsIsomorphic` witness.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe wA wBC vA vB vC uA uB uC

namespace CategoryTheory.Functor.RightDerived.Composition.BoundedBelow

-- Select Mathlib's proved injective derivability structure when forming the derived functors.
attribute [local instance 2000] Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
variable [Abelian A] [Abelian B] [Abelian C]
variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wBC} B] [HasDerivedCategory.{wBC} C]
variable (F : A ⥤ B) [F.Additive] (G : B ⥤ₑ C)
variable [EnoughInjectives A] [EnoughInjectives B]

namespace ExactSecond

/-- If the second functor is exact, its direct action on `D⁺` identifies the two-stage derived
functor with the one-stage right-derived functor of the composite. -/
@[stacks 015M "bounded derived composition with an exact second functor"]
noncomputable def iso :
    Functor.RightDerived.Bounded.functor F ⋙
        ExactFunctor.Derived.Plus.functor G ≅
      Functor.RightDerived.Bounded.functor (F ⋙ G.obj) :=
  Functor.isoWhiskerLeft (Functor.RightDerived.Bounded.functor F)
      (ExactFunctor.Derived.Plus.rightDerivedIso G).symm ≪≫
    (asIso (comparison F G.obj)).symm

/-- The objectwise degree comparison for postcomposition by an exact functor.  Its first factor
commutes the exact action with homology; its second factor applies homology to the canonical
one-stage/two-stage derived comparison. -/
@[stacks 015M "degree comparison with an exact second functor"]
noncomputable def degreeAppIso (i : ℤ) (X : A) :
    G.obj.obj ((Functor.RightDerived.Bounded.degree F i).obj X) ≅
      (Functor.RightDerived.Bounded.degree (F ⋙ G.obj) i).obj X :=
  (ExactFunctor.Derived.Plus.homologyFunctorIso G i).symm.app
      ((Functor.RightDerived.Bounded.functor F).obj
        ((DerivedCategory.Plus.singleFunctor A 0).obj X)) ≪≫
    (DerivedCategory.Plus.homologyFunctor C i).mapIso
      ((iso F G).app ((DerivedCategory.Plus.singleFunctor A 0).obj X))

/-- The objectwise exact-second degree comparisons are natural in the input object. -/
@[stacks 015M "naturality of the exact-second degree comparison"]
theorem degreeAppIso_hom_naturality
    (i : ℤ) {X Y : A} (f : X ⟶ Y) :
    (Functor.RightDerived.Bounded.degree F i ⋙ G.obj).map f ≫
        (degreeAppIso F G i Y).hom =
      (degreeAppIso F G i X).hom ≫
        (Functor.RightDerived.Bounded.degree (F ⋙ G.obj) i).map f := sorry

/-- Right-derived degrees commute canonically with postcomposition by an exact functor. -/
@[stacks 015M "right-derived degrees commute with an exact second functor"]
noncomputable def degreeIso (i : ℤ) :
    Functor.RightDerived.Bounded.degree F i ⋙ G.obj ≅
      Functor.RightDerived.Bounded.degree (F ⋙ G.obj) i :=
  NatIso.ofComponents (degreeAppIso F G i)
    (fun f ↦ degreeAppIso_hom_naturality F G i f)

end ExactSecond

end CategoryTheory.Functor.RightDerived.Composition.BoundedBelow
