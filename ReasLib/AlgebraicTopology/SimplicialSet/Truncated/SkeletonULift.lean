/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Skeletons and universe lifts

This file exposes the canonical comparison isomorphisms showing that truncation and
skeleton functors commute with universe lifts.  Keeping the comparison at the functor
level lets downstream constructions reuse its components and naturality directly.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

noncomputable section

universe w v

namespace SSet.Truncated.sk

/-- The skeleton of a truncated simplicial set commutes with universe lift. -/
@[stacks 018N "truncated skeleton commutes with universe lift"]
noncomputable def uliftIso (n : ℕ) :
    SSet.Truncated.sk.{w} n ⋙ SSet.uliftFunctor.{v, w} ≅
      SSet.Truncated.uliftFunctor.{v, w} n ⋙ SSet.Truncated.sk.{max w v} n :=
  (CategoryTheory.uliftFunctor.{v, w}).lanCompIsoOfPreserves
    (SimplexCategory.Truncated.inclusion n).op

end SSet.Truncated.sk

namespace SSet.truncation

/-- Truncation of a simplicial set commutes with universe lift. -/
@[stacks 018N "truncation commutes with universe lift"]
def uliftIso (n : ℕ) :
    SSet.uliftFunctor.{v, w} ⋙ SSet.truncation.{max w v} n ≅
      SSet.truncation.{w} n ⋙ SSet.Truncated.uliftFunctor.{v, w} n :=
  Iso.refl _

end SSet.truncation

namespace SSet.sk

/-- The skeleton endofunctor on simplicial sets commutes with universe lift. -/
@[stacks 018N "skeleton commutes with universe lift"]
noncomputable def uliftIso (n : ℕ) :
    SSet.sk.{w} n ⋙ SSet.uliftFunctor.{v, w} ≅
      SSet.uliftFunctor.{v, w} ⋙ SSet.sk.{max w v} n :=
  Functor.associator
      (SSet.truncation.{w} n) (SSet.Truncated.sk.{w} n)
      SSet.uliftFunctor.{v, w} ≪≫
    Functor.isoWhiskerLeft (SSet.truncation.{w} n)
      (SSet.Truncated.sk.uliftIso n) ≪≫
    (Functor.associator
      (SSet.truncation.{w} n) (SSet.Truncated.uliftFunctor.{v, w} n)
      (SSet.Truncated.sk.{max w v} n)).symm ≪≫
    Functor.isoWhiskerRight (SSet.truncation.uliftIso n).symm
      (SSet.Truncated.sk.{max w v} n) ≪≫
    Functor.associator
      SSet.uliftFunctor.{v, w} (SSet.truncation.{max w v} n)
      (SSet.Truncated.sk.{max w v} n)

/-- The skeleton adjunction across two type universes, expressed after lifting both source and
target to their common universe. -/
@[stacks 018N "cross-universe lifted skeleton Hom equivalence"]
noncomputable def uliftHomEquiv (n : ℕ) (U : SSet.{w}) (V : SSet.{v}) :
    ((SSet.Truncated.uliftFunctor.{v, w} n).obj ((SSet.truncation n).obj U) ⟶
        (SSet.Truncated.uliftFunctor.{w, v} n).obj ((SSet.truncation n).obj V)) ≃
      ((SSet.uliftFunctor.{v, w}).obj ((SSet.sk n).obj U) ⟶
        (SSet.uliftFunctor.{w, v}).obj V) :=
  ((((SSet.truncation.uliftIso.{w, v} n).app U).symm.homCongr
      ((SSet.truncation.uliftIso.{v, w} n).app V).symm).trans
    (((SSet.skAdj n).homEquiv
      ((SSet.truncation.{max w v} n).obj ((SSet.uliftFunctor.{v, w}).obj U))
      ((SSet.uliftFunctor.{w, v}).obj V)).symm.trans
        (((SSet.sk.uliftIso.{w, v} n).app U).symm.homCongr (Iso.refl _))))

/-- The cross-universe lifted skeleton Hom equivalence is natural under postcomposition. -/
@[stacks 018N "cross-universe lifted skeleton target naturality"]
theorem uliftHomEquiv.comp (n : ℕ) {U : SSet.{w}} {V W : SSet.{v}}
    (f : (SSet.Truncated.uliftFunctor.{v, w} n).obj ((SSet.truncation n).obj U) ⟶
      (SSet.Truncated.uliftFunctor.{w, v} n).obj ((SSet.truncation n).obj V))
    (g : V ⟶ W) :
    uliftHomEquiv n U W
        (f ≫ (SSet.Truncated.uliftFunctor.{w, v} n).map ((SSet.truncation n).map g)) =
      uliftHomEquiv n U V f ≫ (SSet.uliftFunctor.{w, v}).map g := sorry

/-- The cross-universe lifted skeleton Hom equivalence is contravariantly natural in its
source. -/
@[stacks 018N "cross-universe lifted skeleton source naturality"]
theorem uliftHomEquiv.precomp (n : ℕ) {U T : SSet.{w}} {V : SSet.{v}}
    (a : U ⟶ T)
    (f : (SSet.Truncated.uliftFunctor.{v, w} n).obj ((SSet.truncation n).obj T) ⟶
      (SSet.Truncated.uliftFunctor.{w, v} n).obj ((SSet.truncation n).obj V)) :
    uliftHomEquiv n U V
        ((SSet.Truncated.uliftFunctor.{v, w} n).map ((SSet.truncation n).map a) ≫ f) =
      (SSet.uliftFunctor.{v, w}).map ((SSet.sk n).map a) ≫
        uliftHomEquiv n T V f := sorry

end SSet.sk
