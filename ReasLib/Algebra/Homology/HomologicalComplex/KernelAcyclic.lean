module

public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Acyclic kernels of quasi-isomorphisms

This file packages the standard short-exact-sequence criterion saying that the kernel of a
degreewise epimorphic quasi-isomorphism is acyclic.
-/

@[expose] public section

open CategoryTheory.Limits

universe v u w

namespace CategoryTheory.HomologicalComplex

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {ι : Type w} {c : ComplexShape ι}

/-- The kernel of a degreewise epimorphic quasi-isomorphism of homological complexes is acyclic. -/
@[stacks 08P1 "acyclic kernel of a degreewise epimorphic quasi-isomorphism"]
theorem kernel_acyclic_of_quasiIso_of_epi {K L : HomologicalComplex A c} (f : K ⟶ L)
    [QuasiIso f] [∀ i : ι, Epi (f.f i)] :
    (kernel f).Acyclic := sorry

/-- Explicit-proof bridge for the acyclic-kernel criterion. -/
theorem kernel_acyclic_of_quasiIso_of_epi.explicit
    {K L : HomologicalComplex A c} (f : K ⟶ L)
    (hquasi : QuasiIso f) (hepi : ∀ i : ι, Epi (f.f i)) :
    (kernel f).Acyclic := sorry

end CategoryTheory.HomologicalComplex
