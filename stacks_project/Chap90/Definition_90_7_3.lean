/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.Completion

/-!
# Completion of a category cofibered in groupoids over `C_Λ`

The completion of `p : F ⥤ ArtinianLocalAlgCat Λ k` is the functor from formal
objects of `p` to `CompleteLocalAlgCat Λ k` sending a formal object to its
complete local base.
-/

@[expose] public section

open CategoryTheory

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]

/- Definition 90.7.3

The completion of a category cofibered in groupoids is the functor from formal
objects to complete local algebras. -/
@[stacks 06H5] #check (CategoryTheory.Functor.completion :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [CategoryTheory.Functor.IsFibered.InGroupoids p.op],
    FormalObject p ⥤ CompleteLocalAlgCat Λ k)

#check (CategoryTheory.Functor.completion_obj :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [CategoryTheory.Functor.IsFibered.InGroupoids p.op]
    (ξ : FormalObject p),
    (CategoryTheory.Functor.completion p).obj ξ = ξ.base)

#check (CategoryTheory.Functor.completion_map :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [CategoryTheory.Functor.IsFibered.InGroupoids p.op]
    {ξ η : FormalObject p} (a : ξ ⟶ η),
    (CategoryTheory.Functor.completion p).map a = a.base)
