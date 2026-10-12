/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Remark_67_12_5_Opens
public import stacks_project.Chap75.Lemma_75_13_6_PseudoCoherent
public import stacks_project.Chap76.Lemma_76_52_4_Relative
public import stacks_project.Chap99.Lemma_99_16_1_Pullback

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
    (K E : ModuleDerived X) {p q : FieldValuedPoint Y} (h : Points.mk p = Points.mk q) :
    fiberNegativeExtVanish f K E p ↔ fiberNegativeExtVanish f K E q :=
  sorry

/-- The set of points of `|Y|` at which all negative fibre Ext-groups of
`(K, E)` vanish. -/
def negativeExtVanishingSet (f : X ⟶ Y) (K E : ModuleDerived X) : Set (Points Y) :=
  {y | ∀ p : FieldValuedPoint Y, Points.mk p = y → fiberNegativeExtVanish f K E p}

/-- A field-valued point represents an element of `negativeExtVanishingSet` if and
only if its fibre Ext-groups vanish in negative degrees. -/
theorem mem_negativeExtVanishingSet_iff (f : X ⟶ Y) (K E : ModuleDerived X)
    (p : FieldValuedPoint Y) :
    Points.mk p ∈ negativeExtVanishingSet f K E ↔
      fiberNegativeExtVanish f K E p :=
  sorry

/-- For a proper, flat, finitely presented morphism, the negative Ext vanishing
set is open in `|Y|`. -/
theorem isOpen_negativeExtVanishingSet (f : X ⟶ Y) [Proper f] [Flat f]
    [FinitePresentation f] (K E : ModuleDerived X) (hK : IsPseudoCoherent X K)
    (hE : IsPerfectRelativeTo f E) :
    IsOpen (negativeExtVanishingSet f K E) :=
  sorry

/-- The open of `|Y|` cut out by vanishing of negative fibre Ext-groups. -/
def negativeExtVanishingOpen (f : X ⟶ Y) [Proper f] [Flat f]
    [FinitePresentation f] (K E : ModuleDerived X) (hK : IsPseudoCoherent X K)
    (hE : IsPerfectRelativeTo f E) : Opens (Points Y) :=
  Opens.mk (negativeExtVanishingSet f K E)
    (isOpen_negativeExtVanishingSet f K E hK hE)

/-- The carrier of `negativeExtVanishingOpen` is `negativeExtVanishingSet`. -/
theorem negativeExtVanishingOpen_carrier (f : X ⟶ Y) [Proper f] [Flat f]
    [FinitePresentation f] (K E : ModuleDerived X) (hK : IsPseudoCoherent X K)
    (hE : IsPerfectRelativeTo f E) :
    (negativeExtVanishingOpen f K E hK hE).carrier = negativeExtVanishingSet f K E :=
  sorry

/-- The open subspace `W ⊂ Y` on which negative fibre Ext-groups of `(K, E)`
vanish. -/
def negativeExtVanishing (f : X ⟶ Y) [Proper f] [Flat f]
    [FinitePresentation f] (K E : ModuleDerived X) (hK : IsPseudoCoherent X K)
    (hE : IsPerfectRelativeTo f E) : OpenSubspace Y :=
  OpenSubspace.ofOpens (negativeExtVanishingOpen f K E hK hE)

/-- The underlying point-set of `negativeExtVanishing` is
`negativeExtVanishingSet`. -/
theorem negativeExtVanishing_pointsSet (f : X ⟶ Y) [Proper f] [Flat f]
    [FinitePresentation f] (K E : ModuleDerived X) (hK : IsPseudoCoherent X K)
    (hE : IsPerfectRelativeTo f E) :
    (negativeExtVanishing f K E hK hE).pointsSet = negativeExtVanishingSet f K E :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
