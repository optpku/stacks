/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.LowerFace
public import ReasLib.Algebra.Homology.HomologicalComplex.MonoEpi
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 017W

# Degreewise properties reflected by normalized Moore complexes

The normalized Moore functors are equivalences, so ReasLib's generic
`Functor.mono_of_mono_map_f`, `Functor.epi_of_epi_map_f`, and
`Functor.isIso_of_isIso_map_f` own reflection from componentwise properties of any
homological-complex-valued functor. This leaf adds only the chapter-facing lower-face bridge.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicTopology
open scoped Simplicial

universe u v

namespace CategoryTheory.Abelian.DoldKan.N

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {U V : SimplicialObject A}

namespace lowerFace.app

/-- If every degree component of the lower-face normalized map is monomorphic, then every
component of the simplicial map is monomorphic. -/
@[stacks 017W "degreewise monomorphisms from lower-face normalization"]
theorem mono_of_normalized {f : U ⟶ V}
    (h : ∀ i : ℕ, Mono (((N.lowerFace (A := A)).map f).f i)) :
    ∀ i : ℕ, Mono (f.app (op ⦋i⦌)) := sorry

/-- If every degree component of the lower-face normalized map is epimorphic, then every component
of the simplicial map is epimorphic. -/
@[stacks 017W "degreewise epimorphisms from lower-face normalization"]
theorem epi_of_normalized {f : U ⟶ V}
    (h : ∀ i : ℕ, Epi (((N.lowerFace (A := A)).map f).f i)) :
    ∀ i : ℕ, Epi (f.app (op ⦋i⦌)) := sorry

/-- If every degree component of the lower-face normalized map is an isomorphism, then every
component of the simplicial map is an isomorphism. -/
@[stacks 017W "degreewise isomorphisms from lower-face normalization"]
theorem isIso_of_normalized {f : U ⟶ V}
    (h : ∀ i : ℕ, IsIso (((N.lowerFace (A := A)).map f).f i)) :
    ∀ i : ℕ, IsIso (f.app (op ⦋i⦌)) := sorry

end lowerFace.app
end CategoryTheory.Abelian.DoldKan.N
