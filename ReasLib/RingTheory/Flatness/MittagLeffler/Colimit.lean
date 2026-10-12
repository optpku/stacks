/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import ReasLib.LinearAlgebra.UniversallyInjective
public import ReasLib.RingTheory.Flatness.MittagLeffler.TensorProduct
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Directed colimits of Mittag-Leffler modules

@stack 0AS7

This leaf records stability of the Mittag-Leffler condition under directed
colimits whose transition maps are universally injective.
-/

open CategoryTheory CategoryTheory.Limits

universe u v w x

namespace Module.MittagLeffler

/-- Lemma 10.89.9 (0AS7): a directed colimit of Mittag-Leffler modules along
universally injective transition maps is Mittag-Leffler. -/
@[stacks 0AS7]
theorem colimit_of_universallyInjective
    {R : Type u} [CommRing R]
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (F : I ⥤ ModuleCat.{max v w} R)
    [∀ i, Module.MittagLeffler R (F.obj i)]
    (hF : ∀ ⦃i j : I⦄ (hij : i ≤ j),
      LinearMap.UniversallyInjective.{u, max v w, max v w, x}
        ((F.map (homOfLE hij)).hom)) :
    Module.MittagLeffler R (colimit F : ModuleCat.{max v w} R) := sorry

end Module.MittagLeffler
