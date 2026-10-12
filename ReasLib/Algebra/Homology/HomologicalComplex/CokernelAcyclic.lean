/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Acyclic cokernels of quasi-isomorphisms

This file is the monomorphic dual of `HomologicalComplex.KernelAcyclic`.  It packages the
short-exact-sequence criterion saying that the cokernel of a degreewise monomorphic
quasi-isomorphism is acyclic.
-/

@[expose] public section

open CategoryTheory.Limits

universe v u w

namespace CategoryTheory.HomologicalComplex

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {ι : Type w} {c : ComplexShape ι}

/-- The cokernel of a degreewise monomorphic quasi-isomorphism of homological complexes is
acyclic. -/
@[stacks 013Q "acyclic cokernel of a degreewise monomorphic quasi-isomorphism"]
theorem cokernel_acyclic_of_quasiIso_of_mono {K L : HomologicalComplex A c} (f : K ⟶ L)
    (hquasi : QuasiIso f) (hmono : ∀ i : ι, Mono (f.f i)) :
    (cokernel f).Acyclic := sorry

end CategoryTheory.HomologicalComplex
