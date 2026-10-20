/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.FiniteTypeApproximation.SchemeTheoreticImage
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 70.23.3: In Situation 70.23.1, if `X ⟶ B` is quasi-separated and of
finite type, and a good diagram `X ⟶ W` over `B ⟶ B_i` is given as in 70.23.2.1,
then for `i' ≥ i` the scheme-theoretic image `X_{i'}` of
`X ⟶ B_{i'} ×_{B_i} W` satisfies `X = lim_{i' ≥ i} X_{i'}`. -/
@[stacks 0CP9] #check
  (AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximationDiagram.nonempty_isLimit_schemeTheoreticImageCone :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    (c : Cone D) (hc : IsLimit c)
    [∀ j : I, IsNoetherian (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
    (i : I) {X : AlgebraicSpace S} (f : X ⟶ c.pt)
    [QuasiSeparated f] [FiniteType f]
    (approximation : FiniteTypeApproximationDiagram f (c.π.app i))
    [FiniteType approximation.toBi]
    [IsClosedImmersion
      (pullback.lift f approximation.toW approximation.comm.w.symm)]
    (Xi : Over (OrderDual.toDual i) ⥤ AlgebraicSpace S)
    (π : (Functor.const (Over (OrderDual.toDual i))).obj X ⟶ Xi)
    (ι : Xi ⟶ baseChangeOverDiagram D (OrderDual.toDual i) approximation.toBi)
    (himage : ∀ j, IsSchemeTheoreticImage
      ((approximation.baseChangeCone D c).π.app j) (π.app j) (ι.app j)),
    Nonempty (IsLimit (⟨X, π⟩ : Cone Xi)))
