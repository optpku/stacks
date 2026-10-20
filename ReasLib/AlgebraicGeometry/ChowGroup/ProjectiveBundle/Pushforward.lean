/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveBundle.Formula
public import ReasLib.AlgebraicGeometry.ChowGroup.Pushforward
public import ReasLib.AlgebraicGeometry.ChowGroup.Reindex
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.Proper

/-!
# Pushforward from projective bundles

This file defines proper pushforward after pullback and intersection with powers of the
tautological first Chern class on a represented projective bundle.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.ProjectiveBundle.Formula

/-- Proper pushforward after projective-bundle pullback and a specified power of the
tautological first-Chern cap. -/
noncomputable def pushforwardC1PowerCap
    {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [hp : LocallyOfFiniteType p] (E : X.Modules) (q : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank (q + 1) E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)
    (k : ℤ) (s : ℕ) :
    @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k →+
      @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance (k + (q : ℤ) - (s : ℤ)) :=
  (@ChowGroup.map S inferInstance δ inferInstance (Over.mk (π ≫ p)) (Over.mk p)
    (locallyOfFiniteTypeComp hπ p (q + 1)) hp (Over.homMk π)
    (hπ.isProperOfFiniteLocallyFree q) (k + (q : ℤ) - (s : ℤ))).comp
      (pullbackThenC1PowerCap δ p E q π hπ k s)

/-- Evaluating projective-bundle Chern-power pushforward is evaluation of proper pushforward
on the corresponding pullback and Chern-cap class. -/
theorem pushforwardC1PowerCap_apply
    {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [hp : LocallyOfFiniteType p] (E : X.Modules) (q : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank (q + 1) E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)
    (k : ℤ) (s : ℕ)
    (α : @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
      (p.relativeDimensionFunction δ) inferInstance k) :
    pushforwardC1PowerCap δ p E q π hπ k s α =
      @ChowGroup.map S inferInstance δ inferInstance
        (Over.mk (π ≫ p)) (Over.mk p)
        (locallyOfFiniteTypeComp hπ p (q + 1)) hp (Over.homMk π)
        (hπ.isProperOfFiniteLocallyFree q) (k + (q : ℤ) - (s : ℤ))
        (pullbackThenC1PowerCap δ p E q π hπ k s α) := sorry

/-- Proper pushforward after the top tautological first-Chern power, with the output degree
canonically identified with the input degree. -/
noncomputable def pushforwardTopC1PowerCap
    {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (q : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank (q + 1) E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E) (k : ℤ) :
    @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k →+
      @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k :=
  (@AlgebraicGeometry.ChowGroup.reindex X
    (LocallyOfFiniteType.isLocallyNoetherian p)
    (p.relativeDimensionFunction δ) inferInstance
    (k + (q : ℤ) - (q : ℤ)) k
    (add_sub_cancel_right k (q : ℤ))).toAddMonoidHom.comp
      (pushforwardC1PowerCap δ p E q π hπ k q)

/-- Evaluating top projective-bundle Chern-power pushforward is evaluation in degree `q`
followed by the canonical grading transport. -/
theorem pushforwardTopC1PowerCap_apply
    {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (q : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank (q + 1) E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)
    (k : ℤ)
    (α : @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
      (p.relativeDimensionFunction δ) inferInstance k) :
    pushforwardTopC1PowerCap δ p E q π hπ k α =
      @AlgebraicGeometry.ChowGroup.reindex X
        (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance
        (k + (q : ℤ) - (q : ℤ)) k
        (add_sub_cancel_right k (q : ℤ))
        (pushforwardC1PowerCap δ p E q π hπ k q α) := sorry

/-- Below the fiber dimension, proper pushforward of pullback capped with a tautological
first-Chern power vanishes. -/
theorem pushforwardC1PowerCap_eq_zero_of_lt
    {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (q : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank (q + 1) E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)
    (k : ℤ) (s : ℕ) (hs : s < q)
    (α : @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
      (p.relativeDimensionFunction δ) inferInstance k) :
    pushforwardC1PowerCap δ p E q π hπ k s α = 0 := sorry

/-- In the fiber dimension, proper pushforward of pullback capped with the top tautological
first-Chern power is the original Chow class. -/
theorem pushforwardTopC1PowerCap_eq_self
    {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (q : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank (q + 1) E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)
    (k : ℤ)
    (α : @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
      (p.relativeDimensionFunction δ) inferInstance k) :
    pushforwardTopC1PowerCap δ p E q π hπ k α = α := sorry

end AlgebraicGeometry.ChowGroup.ProjectiveBundle.Formula
