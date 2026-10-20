/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Limit.Proper.Eventually
import StacksCheckRecall

open CategoryTheory Limits AlgebraicGeometry

universe u

/- Lemma 32.13.4: let `S` be a scheme and let `X = lim_i X_i` be a directed limit of
schemes over `S` with affine transition morphisms. Let `Y ⟶ X` be a morphism over `S`.
If `Y ⟶ X` is proper, every `X_i` is quasi-compact and quasi-separated, and `Y` is
locally of finite type over `S`, then `Y ⟶ X_i` is proper for all sufficiently large
indices `i`. -/
@[stacks 0EX1] #check (AlgebraicGeometry.Scheme.Limit.exists_eventually_isProper_to_stage :
  ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S Y : Scheme.{u}} (D : OrderDual I ⥤ Scheme.{u})
    (t : D ⟶ (Functor.const (OrderDual I)).obj S) (c : Cone D) (hc : IsLimit c)
    (σlim : c.pt ⟶ S) (hπ : c.π ≫ t = (Functor.const _).map σlim)
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (D.map (homOfLE hii'))]
    (f : Y ⟶ c.pt) (g : Y ⟶ S) [IsProper f] [LocallyOfFiniteType g]
    (hfg : f ≫ σlim = g),
    ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → IsProper (f ≫ c.π.app i))
