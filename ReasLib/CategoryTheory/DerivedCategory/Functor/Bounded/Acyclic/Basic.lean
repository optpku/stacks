/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Above.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Below.Basic
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt
public import ReasLib.Algebra.Homology.HomotopyCategory.Termwise
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Acyclic Objects for Bounded Derived Functors

This leaf records the degree-zero objects of an abelian category at which the
bounded or unbounded derived functor of an additive functor is computed without
a resolution. It also provides the corresponding termwise conditions on bounded
homotopy objects.
-/

open CategoryTheory
open ComplexShape

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

section Right

/-- An object of `𝒜` is right acyclic for the bounded-below derived functor
of `F` when its degree-zero complex computes that functor. -/
@[stacks 0157]
abbrev RightAcyclic.Bounded : ObjectProperty 𝒜 :=
  fun A =>
    RightDerived.ComputesAt
      F.toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso 𝒜)
      ((HomotopyCategory.Plus.singleFunctor 𝒜 0).obj A)

/-- A bounded-below homotopy object is termwise right acyclic for the
bounded-below derived functor of `F` when each of its cochain terms is right
acyclic. -/
@[stacks 0157]
abbrev RightAcyclic.Bounded.Termwise (K : HomotopyCategory.Plus 𝒜) : Prop :=
  HomotopyCategory.Plus.termsIn 𝒜 (RightAcyclic.Bounded F) K

end Right

section UnboundedRight

variable [HasDerivedCategory.{w} 𝒜]

/-- An object of `𝒜` is right acyclic for the unbounded derived functor of `F`
when its degree-zero complex computes that functor. -/
@[stacks 0157]
abbrev RightAcyclic : ObjectProperty 𝒜 :=
  fun A =>
    RightDerived.ComputesAt
      (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso 𝒜 (up ℤ))
      ((HomotopyCategory.singleFunctor 𝒜 0).obj A)

/-- A bounded-below homotopy object is termwise right acyclic for the
unbounded derived functor of `F` when each of its cochain terms is right
acyclic. -/
@[stacks 0157]
abbrev RightAcyclic.Termwise (K : HomotopyCategory.Plus 𝒜) : Prop :=
  HomotopyCategory.Plus.termsIn 𝒜 (RightAcyclic F) K

end UnboundedRight

section Left

/-- An object of `𝒜` is left acyclic for the bounded-above derived functor
of `F` when its degree-zero complex computes that functor. -/
@[stacks 0157]
abbrev LeftAcyclic.Bounded : ObjectProperty 𝒜 :=
  fun A =>
    LeftDerived.ComputesAt
      F.toBoundedAboveDerived
      (HomotopyCategory.Minus.quasiIso 𝒜)
      ((HomotopyCategory.Minus.singleFunctor 𝒜 0).obj A)

/-- A bounded-above homotopy object is termwise left acyclic for the
bounded-above derived functor of `F` when each of its cochain terms is left
acyclic. -/
@[stacks 0157]
abbrev LeftAcyclic.Bounded.Termwise (K : HomotopyCategory.Minus 𝒜) : Prop :=
  HomotopyCategory.Minus.termsIn 𝒜 (LeftAcyclic.Bounded F) K

end Left

section UnboundedLeft

variable [HasDerivedCategory.{w} 𝒜]

/-- An object of `𝒜` is left acyclic for the unbounded derived functor of `F`
when its degree-zero complex computes that functor. -/
@[stacks 0157]
abbrev LeftAcyclic : ObjectProperty 𝒜 :=
  fun A =>
    LeftDerived.ComputesAt
      (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso 𝒜 (up ℤ))
      ((HomotopyCategory.singleFunctor 𝒜 0).obj A)

/-- A bounded-above homotopy object is termwise left acyclic for the
unbounded derived functor of `F` when each of its cochain terms is left
acyclic. -/
@[stacks 0157]
abbrev LeftAcyclic.Termwise (K : HomotopyCategory.Minus 𝒜) : Prop :=
  HomotopyCategory.Minus.termsIn 𝒜 (LeftAcyclic F) K

end UnboundedLeft

end


end CategoryTheory.Functor
