/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.EssentialFiniteness.Basic

/-!
# Finite presentation over valuation rings

This leaf owns finite-presentation results for finite-type algebras and finite modules over a
valuation ring, together with their local essentially-finite-type forms.

@stack 053E
@stack 0GSE
-/

@[expose] public section

universe u v w

namespace Algebra.FinitePresentation

/-- A flat finite-type algebra over a valuation ring is finitely presented. -/
@[stacks 053E "Lemma 15.25.6 (1)"]
theorem ofFlatFiniteTypeValuationRing
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    {B : Type v} [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    [Module.Flat A B] :
    Algebra.FinitePresentation A B := sorry

end Algebra.FinitePresentation

namespace Module.FinitePresentation

/-- A finite module over a finite-type algebra over a valuation ring is
finitely presented when it is flat over the valuation ring. -/
@[stacks 053E "Lemma 15.25.6 (2)"]
theorem ofFiniteFlatFiniteTypeValuationRing
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    {B : Type v} [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    {M : Type w} [AddCommMonoid M] [Module B M] [Module.Finite B M]
    [Module A M] [IsScalarTower A B M] [Module.Flat A M] :
    Module.FinitePresentation B M := sorry

end Module.FinitePresentation

namespace Algebra.EssFinitePresentation

/-- A flat local algebra essentially of finite type over a valuation ring is
essentially of finite presentation. -/
@[stacks 0GSE "Lemma 15.25.7 (1)"]
theorem ofFlatEssFiniteTypeLocalValuationRing
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    {B : Type v} [CommRing B] [Algebra A B] [IsLocalRing B]
    [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B] [Module.Flat A B] :
    Algebra.EssFinitePresentation A B := sorry

end Algebra.EssFinitePresentation

namespace Module.FinitePresentation

/-- A finite module over a local algebra essentially of finite type over a
valuation ring is finitely presented when it is flat over the valuation ring. -/
@[stacks 0GSE "Lemma 15.25.7 (2)"]
theorem ofFiniteFlatEssFiniteTypeLocalValuationRing
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    {B : Type v} [CommRing B] [Algebra A B] [IsLocalRing B]
    [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B]
    {M : Type w} [AddCommMonoid M] [Module B M] [Module.Finite B M]
    [Module A M] [IsScalarTower A B M] [Module.Flat A M] :
    Module.FinitePresentation B M := sorry

end Module.FinitePresentation
