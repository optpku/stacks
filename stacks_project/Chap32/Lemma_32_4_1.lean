/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.DirectedAffine
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
variable [∀ {i j : OrderDual I} (f : i ⟶ j), IsAffineHom (D.map f)]

/- Lemma 32.4.1: the underlying set of a limit of a directed inverse system of schemes with
affine transition morphisms is the inverse limit of the underlying sets. -/
@[stacks 0CUE] #check
  (AlgebraicGeometry.Scheme.Limit.DirectedAffine.bijective_sectionOfCone D c hc :
    Function.Bijective (Types.sectionOfCone (Scheme.forget.mapCone c)))
