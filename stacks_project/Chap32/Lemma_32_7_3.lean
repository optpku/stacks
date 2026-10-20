/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Integral.Approximation
import StacksCheckRecall

open CategoryTheory Limits AlgebraicGeometry

universe u

/- Lemma 32.7.3: an integral morphism into a quasi-compact and quasi-separated scheme is a
directed limit, over the target, of finite morphisms of finite presentation. -/
@[stacks 09YZ] #check
  (AlgebraicGeometry.IsIntegralHom.existsFinitePresentationLimit :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsIntegralHom f]
      [CompactSpace S] [QuasiSeparatedSpace S],
      ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
        (D : OrderDual I ⥤ Over S)
        (π : (Functor.const (OrderDual I)).obj (Over.mk f) ⟶ D),
        Nonempty (IsLimit (⟨Over.mk f, π⟩ : Cone D)) ∧
          ∀ j : I,
            IsFinite (D.obj j).hom ∧ Scheme.Hom.FinitePresentation (D.obj j).hom)
