/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.BaseChange.Pullback
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction

/-!
# Negative Ext vanishing locus

The set of points of `|Y|` at which all negative fibre Ext-groups of a pair
`(K, E)` vanish is an open of `|Y|`, and therefore determines an open subspace
`W ⊂ Y`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open TopologicalSpace
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}



/-- The fibre Ext-groups `Ext⁽i⁾(K_y, E_y)` vanish for all `i < 0`. -/
def fiberNegativeExtVanish (f : X ⟶ Y) (K E : ModuleDerived X)
    (p : FieldValuedPoint Y) : Prop :=
  ∀ i : ℤ, i < 0 →
    Subsingleton (Ext⁽i⁾(fiberPullback f p K, fiberPullback f p E))

/-- Negative fibre Ext vanishing depends only on the point of `|Y|` represented
by a field-valued morphism. -/
theorem fiberNegativeExtVanish_dependsOnlyOnPoint (f : X ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f] (K E : ModuleDerived X)
    (hK : IsPseudoCoherent X K) (hE : IsPerfectRelativeTo f E) {p q : FieldValuedPoint Y} (h : Points.mk p = Points.mk q) :
    fiberNegativeExtVanish f K E p ↔ fiberNegativeExtVanish f K E q := sorry

/-- The set of points of `|Y|` at which all negative fibre Ext-groups of
`(K, E)` vanish. -/
def negativeExtVanishingSet (f : X ⟶ Y) (K E : ModuleDerived X) : Set (Points Y) :=
  {y | ∀ p : FieldValuedPoint Y, Points.mk p = y → fiberNegativeExtVanish f K E p}

/-- A field-valued point represents an element of `negativeExtVanishingSet` if and
only if its fibre Ext-groups vanish in negative degrees. -/
theorem mem_negativeExtVanishingSet_iff (f : X ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f] (K E : ModuleDerived X)
    (hK : IsPseudoCoherent X K) (hE : IsPerfectRelativeTo f E) (p : FieldValuedPoint Y) :
    Points.mk p ∈ negativeExtVanishingSet f K E ↔
      fiberNegativeExtVanish f K E p := by
  constructor
  · intro h
    exact h p rfl
  · intro h q hq
    exact (fiberNegativeExtVanish_dependsOnlyOnPoint f K E hK hE hq).2 h

/-- For a proper, flat, finitely presented morphism, the negative Ext vanishing
set is open in `|Y|`. -/
theorem isOpen_negativeExtVanishingSet (f : X ⟶ Y)
    [Proper f] [Flat f]
    [FinitePresentation f] (K E : ModuleDerived X) (hK : IsPseudoCoherent X K)
    (hE : IsPerfectRelativeTo f E) :
    IsOpen (negativeExtVanishingSet f K E) := sorry

/-- The open of `|Y|` cut out by vanishing of negative fibre Ext-groups. -/
def negativeExtVanishingOpen (f : X ⟶ Y)
    [Proper f] [Flat f]
    [FinitePresentation f] (K E : ModuleDerived X) (hK : IsPseudoCoherent X K)
    (hE : IsPerfectRelativeTo f E) : Opens (Points Y) :=
  Opens.mk (negativeExtVanishingSet f K E)
    (isOpen_negativeExtVanishingSet f K E hK hE)

/-- The carrier of `negativeExtVanishingOpen` is `negativeExtVanishingSet`. -/
theorem negativeExtVanishingOpen_carrier (f : X ⟶ Y)
    [Proper f] [Flat f]
    [FinitePresentation f] (K E : ModuleDerived X) (hK : IsPseudoCoherent X K)
    (hE : IsPerfectRelativeTo f E) :
    (negativeExtVanishingOpen f K E hK hE).carrier = negativeExtVanishingSet f K E := rfl

/-- The open subspace `W ⊂ Y` on which negative fibre Ext-groups of `(K, E)`
vanish. -/
def negativeExtVanishing (f : X ⟶ Y)
    [Proper f] [Flat f]
    [FinitePresentation f] (K E : ModuleDerived X) (hK : IsPseudoCoherent X K)
    (hE : IsPerfectRelativeTo f E) : OpenSubspace Y :=
  OpenSubspace.fromOpens (negativeExtVanishingOpen f K E hK hE)

/-- The underlying point-set of `negativeExtVanishing` is
`negativeExtVanishingSet`. -/
theorem negativeExtVanishing_pointsSet (f : X ⟶ Y)
    [Proper f] [Flat f]
    [FinitePresentation f] (K E : ModuleDerived X) (hK : IsPseudoCoherent X K)
    (hE : IsPerfectRelativeTo f E) :
    (negativeExtVanishing f K E hK hE).pointsSet = negativeExtVanishingSet f K E :=
  OpenSubspace.fromOpens_pointsSet (negativeExtVanishingOpen f K E hK hE)

variable (f : X ⟶ Y) [Proper f] [Flat f] [FinitePresentation f]
variable (K E : ModuleDerived X) (hK : IsPseudoCoherent X K)
variable (hE : IsPerfectRelativeTo f E)

/-- A field-valued point lies in the negative Ext vanishing open if and only if
the fibre Ext-groups `Ext⁽i⁾(K_y, E_y)` vanish for all `i < 0`. -/
theorem mem_negativeExtVanishingOpen_iff (p : FieldValuedPoint Y) :
    Points.mk p ∈ negativeExtVanishingOpen f K E hK hE ↔
      fiberNegativeExtVanish f K E p :=
  mem_negativeExtVanishingSet_iff f K E hK hE p

/-- If `V ⟶ Y` factors through the negative Ext vanishing subspace, then the Ext-groups
`Ext⁽i⁾(K_V, E_V)` vanish for all `i < 0`. -/
theorem negativeExt_eq_zero_of_factors {V : AlgebraicSpace S} (g : V ⟶ Y)
    (h : V ⟶ (negativeExtVanishing f K E hK hE).X)
    (hh : h ≫ (negativeExtVanishing f K E hK hE).ι = g) (i : ℤ) (hi : i < 0) :
    Subsingleton
      (Ext⁽i⁾(baseChangePullback f g K, baseChangePullback f g E)) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
