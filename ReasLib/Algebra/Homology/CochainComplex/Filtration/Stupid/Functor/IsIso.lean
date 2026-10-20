/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.Stupid.Functor

/-!
# Isomorphism transport for the stupid-filtration functor

An isomorphism of cochain complexes induces an isomorphism of their stupidly
filtered complexes, degree by degree and as a bundled filtered morphism.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.CochainComplex.Stupid

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K L : CochainComplex A ℤ}

/-- Every degree component of a stupid-filtration map is an isomorphism when the source map is. -/
@[stacks 0D8Z]
noncomputable instance map_f_isIso (f : K ⟶ L) (n : ℤ) [IsIso f] :
    IsIso ((map f).f n) := sorry

/-- A cochain-complex isomorphism induces an isomorphism of stupid filtrations. -/
@[stacks 0D8Z]
noncomputable instance map_isIso (f : K ⟶ L) [IsIso f] :
    IsIso (map f) := sorry

variable (f : K ⟶ L) [IsIso f]
#synth IsIso ((map f).f 0)
#synth IsIso (map f)

end CategoryTheory.CochainComplex.Stupid
