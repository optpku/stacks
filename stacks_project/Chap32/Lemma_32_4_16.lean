/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.Immersion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

/- Lemma 32.4.16 (1): a closed immersion into the limit descends to every sufficiently large
stage under the stated quasi-compactness and finite-type hypotheses. -/
@[stacks 081B] #check
  (AlgebraicGeometry.Scheme.Limit.exists_eventually_isClosedImmersion_to_stage :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] {S Y : Scheme.{u}}
      (D : OrderDual I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const (OrderDual I)).obj S)
      (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ S)
      (hπ : c.π ≫ t = (Functor.const _).map σlim)
      [∀ i : I, CompactSpace (D.obj i)]
      [∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (D.map (homOfLE hii'))]
      (f : Y ⟶ c.pt) (g : Y ⟶ S) [IsClosedImmersion f] [LocallyOfFiniteType g]
      (hfg : f ≫ σlim = g),
      ∃ i : I, ∀ ⦃i' : I⦄, i ≤ i' → IsClosedImmersion (f ≫ c.π.app i'))

/- Lemma 32.4.16 (2): an immersion into the limit descends to every sufficiently large stage
under the stated quasi-separatedness, quasi-compactness, and finite-type hypotheses. -/
@[stacks 081B] #check
  (AlgebraicGeometry.Scheme.Limit.exists_eventually_isImmersion_to_stage :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] {S Y : Scheme.{u}}
      (D : OrderDual I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const (OrderDual I)).obj S)
      (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ S)
      (hπ : c.π ≫ t = (Functor.const _).map σlim)
      [∀ i : I, QuasiSeparatedSpace (D.obj i)]
      [∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (D.map (homOfLE hii'))]
      [CompactSpace Y]
      (f : Y ⟶ c.pt) (g : Y ⟶ S) [IsImmersion f] [LocallyOfFiniteType g]
      (hfg : f ≫ σlim = g),
      ∃ i : I, ∀ ⦃i' : I⦄, i ≤ i' → IsImmersion (f ≫ c.π.app i'))

/- Lemma 32.4.16 (3): an isomorphism to the limit descends to every sufficiently large stage
under the stated quasi-compactness, finite-type, closed-transition, and finite-presentation
hypotheses. -/
@[stacks 081B] #check
  (AlgebraicGeometry.Scheme.Limit.exists_eventually_isIso_to_stage :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] {S Y : Scheme.{u}}
      (D : OrderDual I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const (OrderDual I)).obj S)
      (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ S)
      (hπ : c.π ≫ t = (Functor.const _).map σlim)
      [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, LocallyOfFiniteType (t.app i)]
      [∀ {i i' : I} (hii' : i ≤ i'), IsClosedImmersion (D.map (homOfLE hii'))]
      (f : Y ⟶ c.pt) (g : Y ⟶ S) [IsIso f] [LocallyOfFinitePresentation g]
      (hfg : f ≫ σlim = g),
      ∃ i : I, ∀ ⦃i' : I⦄, i ≤ i' → IsIso (f ≫ c.π.app i'))
