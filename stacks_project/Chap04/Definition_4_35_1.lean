/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]
variable (p : S ⥤ C)

/- Definition 4.35.1: a functor `p : 𝒮 ⥤ 𝒞` is fibred in groupoids if it is fibered and every
morphism of `𝒮` is strongly Cartesian over its image. The canonical owner uses the equivalent
Cartesian formulation. -/
@[stacks 003T]
#check (Functor.IsFibered.InGroupoids p : Prop)

/- The source formulation using strongly Cartesian morphisms is equivalent to the canonical
owner. -/
#check Functor.IsFibered.InGroupoids.iff_isFibered_allStronglyCartesian

end CategoryTheory
