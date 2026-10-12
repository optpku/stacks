/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Monomorphic and Epimorphic Quasi-Isomorphisms

This file packages the intersections of quasi-isomorphisms with categorical monomorphisms and
epimorphisms.  Degreewise characterizations belong in the separate `HomologicalComplex.MonoEpi`
API and are not built into these denominator systems.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace HomologicalComplex

variable (C : Type u) [Category.{v} C] [HasZeroMorphisms C] [CategoryWithHomology C]
variable {I : Type w} (c : ComplexShape I)

/-- Quasi-isomorphisms that are also monomorphisms of homological complexes. -/
@[stacks 05T6 "monomorphic quasi-isomorphisms of complexes"]
def quasiIsoMono : MorphismProperty (HomologicalComplex C c) :=
  HomologicalComplex.quasiIso C c ⊓ MorphismProperty.monomorphisms _

/-- Membership in `quasiIsoMono C c` is exactly the conjunction of quasi-isomorphism and
monomorphism. -/
@[stacks 05T6 "membership in monomorphic quasi-isomorphisms"]
theorem mem_quasiIsoMono_iff {K L : HomologicalComplex C c} (f : K ⟶ L) :
    quasiIsoMono C c f ↔ QuasiIso f ∧ Mono f := sorry

/-- Monomorphic quasi-isomorphisms are quasi-isomorphisms. -/
@[stacks 05T6 "monomorphic quasi-isomorphisms are quasi-isomorphisms"]
theorem quasiIsoMono_le_quasiIso :
    quasiIsoMono C c ≤ HomologicalComplex.quasiIso C c := sorry

/-- Monomorphic quasi-isomorphisms are monomorphisms. -/
@[stacks 05T6 "monomorphic quasi-isomorphisms are monomorphisms"]
theorem quasiIsoMono_le_monomorphisms :
    quasiIsoMono C c ≤ MorphismProperty.monomorphisms _ := sorry

/-- Quasi-isomorphisms that are also epimorphisms of homological complexes. -/
@[stacks 05T7 "epimorphic quasi-isomorphisms of complexes"]
def quasiIsoEpi : MorphismProperty (HomologicalComplex C c) :=
  HomologicalComplex.quasiIso C c ⊓ MorphismProperty.epimorphisms _

/-- Membership in `quasiIsoEpi C c` is exactly the conjunction of quasi-isomorphism and
epimorphism. -/
@[stacks 05T7 "membership in epimorphic quasi-isomorphisms"]
theorem mem_quasiIsoEpi_iff {K L : HomologicalComplex C c} (f : K ⟶ L) :
    quasiIsoEpi C c f ↔ QuasiIso f ∧ Epi f := sorry

/-- Epimorphic quasi-isomorphisms are quasi-isomorphisms. -/
@[stacks 05T7 "epimorphic quasi-isomorphisms are quasi-isomorphisms"]
theorem quasiIsoEpi_le_quasiIso :
    quasiIsoEpi C c ≤ HomologicalComplex.quasiIso C c := sorry

/-- Epimorphic quasi-isomorphisms are epimorphisms. -/
@[stacks 05T7 "epimorphic quasi-isomorphisms are epimorphisms"]
theorem quasiIsoEpi_le_epimorphisms :
    quasiIsoEpi C c ≤ MorphismProperty.epimorphisms _ := sorry

end HomologicalComplex


