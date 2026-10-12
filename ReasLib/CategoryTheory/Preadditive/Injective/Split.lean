/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

@[expose] public section

/-!
# Split morphisms from injective and projective objects

Injectivity splits every monomorphism whose source is injective.  Dually, projectivity splits
every epimorphism whose target is projective.  These statements are independent of any chosen
abelian or exact structure and form the reusable core of admissibility criteria for complexes.
-/

open CategoryTheory

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Injective

/-- A monomorphism whose source is injective is split monic. -/
theorem isSplitMono {X Y : C} [Injective X] (f : X ⟶ Y) [Mono f] :
    IsSplitMono f := sorry

end Injective

namespace Projective

/-- An epimorphism whose target is projective is split epic. -/
theorem isSplitEpi {X Y : C} [Projective Y] (f : X ⟶ Y) [Epi f] :
    IsSplitEpi f := sorry

end Projective

end CategoryTheory
