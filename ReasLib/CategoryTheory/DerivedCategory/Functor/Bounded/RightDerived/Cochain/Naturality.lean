/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Functor.Naturality.Plus
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Cochain
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Naturality
import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of maps into bounded-below right-derived values

The canonical map induced by a cochain map is compatible with natural transformations of
additive functors.  This is the public bridge between the termwise cochain-level action and the
natural transformation on canonical bounded-below right-derived functors.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w vA vB uA uB

namespace CategoryTheory.Functor.RightDerived.Bounded

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]

/-- Postcomposing a cochain map with an additive natural transformation agrees with
postcomposing its canonical bounded-below right-derived map with the induced transformation. -/
@[reassoc, stacks 01F8 "functoriality of the bounded right-derived map from a cochain map"]
theorem fromCochainMap_map
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [G.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (τ : F ⟶ G) {L : CochainComplex.Plus B} {K : CochainComplex.Plus A}
    (φ : L ⟶ F.mapCochainComplexPlus.obj K) :
    fromCochainMap F φ ≫
        (map τ).app
          (DerivedCategory.Plus.Qh.obj
            ((HomotopyCategory.Plus.quotient A).obj K)) =
      fromCochainMap G
        (φ ≫ (Functor.Cochain.Plus.natTrans τ).app K) := sorry

end CategoryTheory.Functor.RightDerived.Bounded
