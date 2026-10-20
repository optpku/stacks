module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic
public import ReasLib.CategoryTheory.Functor.Exactness.ShortExact
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
import Mathlib.Tactic.CrossRefAttribute

/-!
# Short exact sequences of bounded-above left-acyclic objects

This file is the left-derived dual of the bounded-below right-acyclic short-exact API.  It records
extension closure, the three useful acyclicity propagation rules, and the corresponding criteria
for a right exact functor to preserve a short exact row.
-/

@[expose] public section

open CategoryTheory.Limits

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B] [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteColimits F]
  [F.toBoundedAboveDerived.HasPointwiseLeftDerivedFunctor
    (HomotopyCategory.Minus.quasiIso A)]

/-- Stacks 015D: bounded-above left-acyclic objects for a right exact additive functor are closed
under short exact extensions. -/
@[stacks 015D]
theorem LeftAcyclic.Bounded.isClosedUnderExtensions :
    ObjectProperty.IsClosedUnderExtensions
      (LeftAcyclic.Bounded F : ObjectProperty A) := sorry

attribute [instance] LeftAcyclic.Bounded.isClosedUnderExtensions

/-- Stacks 015D (1): the middle term of a short exact complex is bounded-above left acyclic when
both outer terms are. -/
@[stacks 015D]
theorem LeftAcyclic.Bounded.middle_of_shortExact
    {S : ShortComplex A} (hS : S.ShortExact)
    (h₁ : LeftAcyclic.Bounded F S.X₁) (h₃ : LeftAcyclic.Bounded F S.X₃) :
    LeftAcyclic.Bounded F S.X₂ := sorry

/-- Stacks 015D: the image of the left morphism of a short exact complex is monic when both
outer terms are bounded-above left acyclic. -/
@[stacks 015D]
theorem LeftAcyclic.Bounded.mono_map_f_of_ends
    {S : ShortComplex A} (hS : S.ShortExact)
    (h₁ : LeftAcyclic.Bounded F S.X₁) (h₃ : LeftAcyclic.Bounded F S.X₃) :
    Mono (F.map S.f) := sorry

/-- Stacks 015D (2): a right exact additive functor maps a short exact complex to a short exact
complex when both outer terms are bounded-above left acyclic. -/
@[stacks 015D]
theorem LeftAcyclic.Bounded.map_shortExact_of_ends
    {S : ShortComplex A} (hS : S.ShortExact)
    (h₁ : LeftAcyclic.Bounded F S.X₁) (h₃ : LeftAcyclic.Bounded F S.X₃) :
    (S.map F).ShortExact := sorry

/-- Stacks 015D (3): the kernel term of a short exact complex is bounded-above left acyclic when
its middle and cokernel terms are. -/
@[stacks 015D]
theorem LeftAcyclic.Bounded.kernel_of_shortExact
    {S : ShortComplex A} (hS : S.ShortExact)
    (h₂ : LeftAcyclic.Bounded F S.X₂) (h₃ : LeftAcyclic.Bounded F S.X₃) :
    LeftAcyclic.Bounded F S.X₁ := sorry

/-- Stacks 015D (4): a right exact additive functor maps a short exact complex to a short exact
complex when its middle and cokernel terms are bounded-above left acyclic. -/
@[stacks 015D]
theorem LeftAcyclic.Bounded.map_shortExact_of_middle_right
    {S : ShortComplex A} (hS : S.ShortExact)
    (h₂ : LeftAcyclic.Bounded F S.X₂) (h₃ : LeftAcyclic.Bounded F S.X₃) :
    (S.map F).ShortExact := sorry

/-- Stacks 015D (5): the cokernel term of a short exact complex is bounded-above left acyclic
when its first two terms are and the image of the left morphism is monic. -/
@[stacks 015D]
theorem LeftAcyclic.Bounded.cokernel_of_shortExact_of_mono_map_f
    {S : ShortComplex A} (hS : S.ShortExact)
    (h₁ : LeftAcyclic.Bounded F S.X₁) (h₂ : LeftAcyclic.Bounded F S.X₂)
    (h_mono : Mono (F.map S.f)) :
    LeftAcyclic.Bounded F S.X₃ := sorry

end CategoryTheory.Functor
