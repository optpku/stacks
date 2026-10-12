/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.Iterated
public import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Tactic.CrossRefAttribute

/-!
# Splittings under iterated localization

A splitting obtained after two successive restrictions can be transported across the
canonical iterated-slice equivalence to a splitting after one direct restriction.  The
component formulas make this transport usable without unfolding the equivalence.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w z

namespace SheafOfModules.Localization.Iterated

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{w})

/-- Transport a splitting after restriction to `U` and then `V : C / U` to a splitting
after direct restriction to the underlying object `V.left`. -/
@[stacks 0B38 "flattening an iterated local splitting"]
noncomputable def flattenSplitting {S : ShortComplex (SheafOfModules.{z} R)}
    {U : C} {V : Over U}
    (s : ((S.map (restriction R U)).map (restriction (R.over U) V)).Splitting) :
    (S.map (restriction R V.left)).Splitting :=
  (s.map (equivalence R U V).functor).ofIso
    (S.mapNatIso (restrictionIso R U V))

/-- The retraction of `flattenSplitting` is obtained by applying the iterated-slice
equivalence to the original retraction and conjugating by `restrictionIso`. -/
@[simp, stacks 0B38 "retraction of a flattened local splitting"]
theorem flattenSplitting_r {S : ShortComplex (SheafOfModules.{z} R)}
    {U : C} {V : Over U}
    (s : ((S.map (restriction R U)).map (restriction (R.over U) V)).Splitting) :
    (flattenSplitting R s).r =
      (S.mapNatIso (restrictionIso R U V)).inv.τ₂ ≫
        (equivalence R U V).functor.map s.r ≫
          (S.mapNatIso (restrictionIso R U V)).hom.τ₁ := sorry

/-- The section of `flattenSplitting` is obtained by applying the iterated-slice
equivalence to the original section and conjugating by `restrictionIso`. -/
@[simp, stacks 0B38 "section of a flattened local splitting"]
theorem flattenSplitting_s {S : ShortComplex (SheafOfModules.{z} R)}
    {U : C} {V : Over U}
    (s : ((S.map (restriction R U)).map (restriction (R.over U) V)).Splitting) :
    (flattenSplitting R s).s =
      (S.mapNatIso (restrictionIso R U V)).inv.τ₃ ≫
        (equivalence R U V).functor.map s.s ≫
          (S.mapNatIso (restrictionIso R U V)).hom.τ₂ := sorry

end SheafOfModules.Localization.Iterated
