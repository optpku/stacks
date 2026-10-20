/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Tactic.CrossRefAttribute

/-!
# Degreewise properties of maps on cycles

This file owns properties of a homological-complex morphism that are expressed through the
induced maps on cycles.  Keeping the predicate on the underlying complex lets differential
graded module models reuse it without duplicating representation-specific definitions.
@stack 0GSQ
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace HomologicalComplex

variable {R : Type*} [Semiring R]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear R C]
variable {ι : Type*} {c : ComplexShape ι}
variable {K L : HomologicalComplex C c}
variable [∀ i, K.HasHomology i] [∀ i, L.HasHomology i]

/-- Taking homology commutes with scalar multiplication of a morphism of homological complexes. -/
@[simp, stacks 0GSQ "homology maps preserve scalar multiplication"]
theorem homologyMap_smul (r : R) (φ : K ⟶ L) (i : ι) :
    homologyMap (r • φ) i = r • homologyMap φ i := sorry

end HomologicalComplex

namespace HomologicalComplex.Hom

variable {C : Type u} [Category.{v} C] [Limits.HasZeroMorphisms C]
variable {ι : Type*} {c : ComplexShape ι}
variable {K L : HomologicalComplex C c}
variable [∀ i, K.HasHomology i] [∀ i, L.HasHomology i]

/-- A morphism of homological complexes is epic on cycles when its induced cycles map is epic
in every degree. -/
@[stacks 0FSE "epimorphic on cycles"]
def EpiOnCycles (f : K ⟶ L) : Prop :=
  ∀ i : ι, Epi (HomologicalComplex.cyclesMap f i)

/-- Being epic on cycles is the degreewise epimorphism condition on the induced cycles maps. -/
theorem epiOnCycles_iff (f : K ⟶ L) :
    f.EpiOnCycles ↔ ∀ i : ι, Epi (HomologicalComplex.cyclesMap f i) := sorry

namespace EpiOnCycles

/-- An epic-on-cycles morphism has an epic induced map in each specified degree. -/
theorem epi {f : K ⟶ L} (hf : f.EpiOnCycles) (i : ι) :
    Epi (HomologicalComplex.cyclesMap f i) := sorry

end EpiOnCycles

end HomologicalComplex.Hom

end
