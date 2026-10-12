/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.Objects.Construction

@[expose] public section

universe v uC uS

namespace CategoryTheory

variable {C : Type uC} [Category.{v} C]
variable {S : Type uS} [Category.{v} S]
variable (p : S ⥤ C) [Functor.IsFibered.InGroupoids p]

/- Lemma 4.35.12: if `p : S ⥤ C` is fibred in groupoids, then the projection from its absolute
inertia is again fibred in groupoids.  The reusable owner is the raw self-relative-inertia
instance `RelativeInertia.Projection.Groupoids.self`. -/
@[stacks 042I]
#check (RelativeInertia.Projection.Groupoids.self p :
  Functor.IsFibered.InGroupoids (RelativeInertia.projection p p))

end CategoryTheory
