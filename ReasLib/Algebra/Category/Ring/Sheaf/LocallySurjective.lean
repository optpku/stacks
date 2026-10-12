/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.Ring.Sheaf
public import ReasLib.CategoryTheory.Sites.LocallySurjective

/-!
# Local surjectivity for underlying ring sheaves

This file records how local surjectivity behaves when a commutative-ring-valued sheaf is
regarded as a ring-valued sheaf.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- Forgetting commutativity preserves local surjectivity of a morphism of commutative
ring sheaves. -/
instance ringSheafOfCommMap_isLocallySurjective
    {R S : Sheaf J CommRingCat.{w}} (f : R ⟶ S) [IsLocallySurjective f] :
    IsLocallySurjective (ringSheafOfCommMap f) := sorry

end CategoryTheory.Sheaf
