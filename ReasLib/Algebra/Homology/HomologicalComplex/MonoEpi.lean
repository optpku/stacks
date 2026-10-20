/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Degreewise monomorphisms and epimorphisms of homological complexes

This module packages the converse direction to the core constructors
`HomologicalComplex.mono_of_mono_f` and `HomologicalComplex.epi_of_epi_f` into degreewise
characterizations valid for every complex shape.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w u' v'

namespace HomologicalComplex

variable {A : Type u} [Category.{v} A]
variable {ι : Type w} {c : ComplexShape ι}

section Mono

variable [HasZeroMorphisms A] [HasPullbacks A]

/-- A morphism of homological complexes is monomorphic exactly when every component is
monomorphic. -/
@[stacks 010Y "degreewise monomorphisms of chain complexes", stacks 0114 "degreewise monomorphisms of cochain complexes"]
theorem mono_iff_mono_f {K L : HomologicalComplex A c} (φ : K ⟶ L) :
    Mono φ ↔ ∀ i : ι, Mono (φ.f i) := sorry

end Mono

section Epi

variable [HasZeroMorphisms A] [HasPushouts A]

/-- A morphism of homological complexes is epimorphic exactly when every component is
epimorphic. -/
@[stacks 010Y "degreewise epimorphisms of chain complexes", stacks 0114 "degreewise epimorphisms of cochain complexes"]
theorem epi_iff_epi_f {K L : HomologicalComplex A c} (φ : K ⟶ L) :
    Epi φ ↔ ∀ i : ι, Epi (φ.f i) := sorry

end Epi

end HomologicalComplex

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C]
variable {A : Type u'} [Category.{v'} A] [HasZeroMorphisms A]
variable {ι : Type w} {c : ComplexShape ι}

/-- A functor to homological complexes reflects a monomorphism as soon as all components of its
image are monomorphisms. -/
@[stacks 010Y "reflection from degreewise chain-complex monomorphisms",
  stacks 0114 "reflection from degreewise cochain-complex monomorphisms"]
theorem mono_of_mono_map_f (F : C ⥤ HomologicalComplex A c)
    [F.ReflectsMonomorphisms] {X Y : C} {f : X ⟶ Y}
    (h : ∀ i : ι, Mono ((F.map f).f i)) : Mono f := sorry

/-- A functor to homological complexes reflects an epimorphism as soon as all components of its
image are epimorphisms. -/
@[stacks 010Y "reflection from degreewise chain-complex epimorphisms",
  stacks 0114 "reflection from degreewise cochain-complex epimorphisms"]
theorem epi_of_epi_map_f (F : C ⥤ HomologicalComplex A c)
    [F.ReflectsEpimorphisms] {X Y : C} {f : X ⟶ Y}
    (h : ∀ i : ι, Epi ((F.map f).f i)) : Epi f := sorry

/-- A functor to homological complexes reflects an isomorphism as soon as all components of its
image are isomorphisms. -/
@[stacks 010Y "reflection from degreewise chain-complex isomorphisms",
  stacks 0114 "reflection from degreewise cochain-complex isomorphisms"]
theorem isIso_of_isIso_map_f (F : C ⥤ HomologicalComplex A c)
    [F.ReflectsIsomorphisms] {X Y : C} {f : X ⟶ Y}
    (h : ∀ i : ι, IsIso ((F.map f).f i)) : IsIso f := sorry

end CategoryTheory.Functor


