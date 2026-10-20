/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Truncated
import Mathlib.Tactic.CrossRefAttribute

/-!
# Epimorphisms and monomorphisms in truncated simplex categories

This file relates categorical epimorphisms and monomorphisms in a truncated simplex category to
the corresponding properties of their underlying simplex-category morphisms.  The one-way
instances expose the canonical passage to the underlying morphism without creating an instance
cycle.
-/

@[expose] public section

open CategoryTheory

namespace SimplexCategory.Truncated

variable {n : ℕ} {X Y : SimplexCategory.Truncated n}

namespace inclusion

/-- The inclusion of a truncated simplex category preserves monomorphisms. -/
@[stacks 017P "truncated simplex inclusion preserves monomorphisms"]
instance preservesMonomorphisms (n : ℕ) :
    (SimplexCategory.Truncated.inclusion n).PreservesMonomorphisms := sorry

/-- The inclusion of a truncated simplex category preserves epimorphisms. -/
@[stacks 017P "truncated simplex inclusion preserves epimorphisms"]
instance preservesEpimorphisms (n : ℕ) :
    (SimplexCategory.Truncated.inclusion n).PreservesEpimorphisms := sorry

end inclusion

/-- A morphism of truncated simplices is monic exactly when its underlying monotone map is
injective. -/
@[stacks 017P "monomorphisms of truncated simplices"]
theorem mono_iff_injective (f : X ⟶ Y) :
    Mono f ↔ Function.Injective f.hom.toOrderHom := sorry

/-- A morphism of truncated simplices is epic exactly when its underlying monotone map is
surjective. -/
@[stacks 017P "epimorphisms of truncated simplices"]
theorem epi_iff_surjective (f : X ⟶ Y) :
    Epi f ↔ Function.Surjective f.hom.toOrderHom := sorry

/-- Monicity in a truncated simplex category agrees with monicity of the underlying
simplex-category morphism. -/
@[stacks 017P "underlying monomorphism of truncated simplices"]
theorem mono_iff_mono_hom (f : X ⟶ Y) : Mono f ↔ Mono f.hom := sorry

/-- Epicity in a truncated simplex category agrees with epicity of the underlying
simplex-category morphism. -/
@[stacks 017P "underlying epimorphism of truncated simplices"]
theorem epi_iff_epi_hom (f : X ⟶ Y) : Epi f ↔ Epi f.hom := sorry

/-- The underlying simplex-category morphism of a monomorphism of truncated simplices is
monic. -/
@[stacks 017P "canonical underlying monomorphism instance"]
instance hom_mono (f : X ⟶ Y) [Mono f] : Mono f.hom := sorry

/-- The underlying simplex-category morphism of an epimorphism of truncated simplices is
epic. -/
@[stacks 017P "canonical underlying epimorphism instance"]
instance hom_epi (f : X ⟶ Y) [Epi f] : Epi f.hom := sorry

end SimplexCategory.Truncated
