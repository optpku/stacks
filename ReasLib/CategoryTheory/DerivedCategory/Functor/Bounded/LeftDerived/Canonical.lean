module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.LeftDerived.Comparison
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.Existence
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Canonical Bounded-Above Left Derived Functor

This file provides the bounded-above counterpart of the canonical bounded-below right-derived
API: the degree-zero embedding, the total left derived functor, its degree functors, and the
resolution-independent degreewise vanishing predicate.
-/

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe w vA vB uA uB

namespace CategoryTheory.Functor.LeftDerived.Bounded

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  (F : A ⥤ B) [F.Additive]

/-- Enough bounded left-acyclic objects canonically provide the bounded-above left derived
functor required by the degree API. -/
@[stacks 05TA]
noncomputable instance hasDerived
    [ObjectProperty.HasEpiCover (fun object : A => LeftDerived.ComputesAt F.toBoundedAboveDerived
      (HomotopyCategory.Minus.quasiIso A)
      ((HomotopyCategory.Minus.singleFunctor A 0).obj object))] :
    F.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A) := sorry

/-- The canonical bounded-above left derived functor of `F`. -/
@[stacks 015A]
abbrev functor
    [F.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)] :
    DerivedCategory.Minus A ⥤ DerivedCategory.Minus B :=
  F.toBoundedAboveDerived.totalLeftDerived
    (DerivedCategory.Minus.Qh A)
    (HomotopyCategory.Minus.quasiIso A)

/-- The canonical localization counit of the bounded-above left derived
functor. -/
@[stacks 015A]
noncomputable abbrev counit
    [F.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)] :
    DerivedCategory.Minus.Qh A ⋙ functor F ⟶
      F.toBoundedAboveDerived :=
  F.toBoundedAboveDerived.totalLeftDerivedCounit
    (DerivedCategory.Minus.Qh A)
    (HomotopyCategory.Minus.quasiIso A)

/-- The degree-`i` functor of the canonical bounded-above left derived functor. -/
@[stacks 015A]
abbrev degree
    [F.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    (i : ℤ) : A ⥤ B :=
  LeftDerived.degree (functor F) i

/-- The homological degree `n` of the canonical bounded-above left derived
functor, i.e. its cohomology in degree `-n`. -/
@[stacks 015A]
abbrev homologicalDegree
    [F.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    (n : ℕ) : A ⥤ B :=
  LeftDerived.homologicalDegree (functor F) n

/-- The canonical comparison from the zeroth left-derived functor to the
underived functor. -/
@[stacks 015A]
noncomputable abbrev zero
    [F.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)] :
    degree F 0 ⟶ F :=
  LeftDerived.zero F (functor F) (counit F)

namespace Vanishes

/-- The canonical bounded-above left-derived functor vanishes in homological degree `n`. -/
@[stacks 07K8]
abbrev inDegree
    [F.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    (n : ℕ) : Prop :=
  IsZero (homologicalDegree F n)

/-- Degreewise vanishing of the bounded-above left derived functor is equivalent to objectwise
vanishing. -/
@[stacks 07K8]
theorem inDegree_iff
    [F.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    (n : ℕ) :
    inDegree F n ↔
      ∀ X : A, IsZero ((homologicalDegree F n).obj X) := sorry

end Vanishes

end CategoryTheory.Functor.LeftDerived.Bounded
