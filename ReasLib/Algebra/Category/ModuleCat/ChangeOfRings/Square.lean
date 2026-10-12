/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Commutative Squares of Module-Category Base Change

@stack 0D2E

This leaf packages the two extension-of-scalars routes attached to a
commutative square of commutative rings.  It assumes only commutativity of the
four ring maps: pushout, flatness, and finiteness hypotheses belong to later
applications, not to this categorical owner.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Limits.CategoricalPullback

universe u

noncomputable section

namespace ModuleCat

variable {C D Cp Dp : Type u}
variable [CommRing C] [CommRing D] [CommRing Cp] [CommRing Dp]

/-- The categorical commutative square of extension-of-scalars functors
attached to a commutative square of ring maps.  The structural isomorphism is
the composite of the two canonical `extendScalarsComp` comparisons and the
given equality of composite ring maps. -/
@[stacks 0D2E, stacks 08KI, stacks 08KL "canonical module-category base-change square"]
noncomputable def extendScalarsCommSq
    (f : D →+* C) (g : Cp →+* C) (p : Dp →+* D) (q : Dp →+* Cp)
    (hcomm : f.comp p = g.comp q) :
    CatCommSqOver (extendScalars f) (extendScalars g) (ModuleCat Dp) where
  fst := extendScalars p
  snd := extendScalars q
  iso := (extendScalarsComp p f).symm ≪≫
    eqToIso (congrArg (fun h ↦ extendScalars h) hcomm) ≪≫
    extendScalarsComp q g

/-- The functor from `ModuleCat Dp` to the categorical pullback induced by a
commutative square of ring maps.  It is derived from
`ModuleCat.extendScalarsCommSq`, so the two module components and their
comparison are not repackaged independently. -/
@[stacks 0D2E, stacks 08KI, stacks 08KL "15.5.3.1 canonical module base-change functor"]
noncomputable def extendScalarsToPullback
    (f : D →+* C) (g : Cp →+* C) (p : Dp →+* D) (q : Dp →+* Cp)
    (hcomm : f.comp p = g.comp q) :
    ModuleCat Dp ⥤ CategoricalPullback (extendScalars f) (extendScalars g) :=
  (CatCommSqOver.toFunctorToCategoricalPullback
    (extendScalars f) (extendScalars g) (ModuleCat Dp)).obj
      (extendScalarsCommSq f g p q hcomm)

end ModuleCat
