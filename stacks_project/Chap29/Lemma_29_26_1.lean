/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Flat
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 29.26.1 (1): support gives a bijection from flat closed subschemes to closed subsets
stable under generalization. -/
@[stacks 04PW] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.flatSupport_bijective :
    ∀ X : Scheme.{u},
      Function.Bijective (AlgebraicGeometry.Scheme.IdealSheafData.flatSupport X))

/- Lemma 29.26.1 (2): every morphism whose range lies in a flat closed subscheme factors
through that closed subscheme. -/
@[stacks 04PW] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.exists_lift_of_flat_of_range_subset :
    ∀ {X Y : Scheme.{u}} (I : X.IdealSheafData) (hI : Flat I.subschemeι) (g : Y ⟶ X),
      Set.range g ⊆ (I.support : Set X) →
        ∃ g' : Y ⟶ I.subscheme, g' ≫ I.subschemeι = g)
