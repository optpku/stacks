/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Functor.Naturality.Minus
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.LeftDerived.Cochain
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.LeftDerived.Naturality
import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of maps out of bounded-above left-derived values

The canonical map induced by a cochain map is compatible with natural transformations of
additive functors.  This is the public bridge between the termwise cochain-level action and the
natural transformation on canonical bounded-above left-derived functors.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w vA vB uA uB

namespace CategoryTheory.Functor.LeftDerived.Bounded

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]

/-- Precomposing a cochain map with an additive natural transformation agrees with
precomposing its canonical bounded-above left-derived map with the induced transformation. -/
@[reassoc, stacks 01F8 "functoriality of the bounded left-derived map from a cochain map"]
theorem fromCochainMap_map
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [F.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    [G.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    (τ : F ⟶ G) {K : CochainComplex.Minus A} {L : CochainComplex.Minus B}
    (φ : (Functor.Cochain.Minus.map G).obj K ⟶ L) :
    (map τ).app
          ((DerivedCategory.Minus.Qh A).obj
            ((HomotopyCategory.Minus.quotient A).obj K)) ≫
        fromCochainMap G φ =
      fromCochainMap F
        ((Functor.Cochain.Minus.natTrans τ).app K ≫ φ) := sorry

end CategoryTheory.Functor.LeftDerived.Bounded
