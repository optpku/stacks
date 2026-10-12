/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Sites.EpiMono

/-!
# Locally injective morphisms of sheaves

This leaf records the categorical characterization of locally injective
morphisms between `Type`-valued sheaves.  It belongs beside the local
predicate rather than in a chapter-specific application.
-/

@[expose] public section

universe u v w

namespace CategoryTheory

namespace Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A morphism of `Type`-valued sheaves is locally injective exactly when it
is a monomorphism. -/
@[stacks 00WN "(1)"]
theorem isLocallyInjective_iff_mono {F G : Sheaf J (Type w)} (phi : F ⟶ G) :
    IsLocallyInjective phi ↔ Mono phi := sorry

end Sheaf

end CategoryTheory
