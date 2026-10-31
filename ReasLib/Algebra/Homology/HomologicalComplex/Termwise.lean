/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.HomologicalComplex.Termwise.Regular

/-!
# Termwise Finiteness Conditions for Module-Valued Complexes

This file owns shape-independent predicates on the terms of a module-valued homological complex.
Chain and cochain complex APIs specialize these predicates instead of maintaining independent
copies.
@stack 064Q
-/

@[expose] public section

open CategoryTheory
open scoped nonZeroDivisors

universe u v

namespace HomologicalComplex

variable {R : Type u} [Ring R]
variable {ι : Type v} {c : ComplexShape ι}

/-- A module-valued homological complex is termwise free when each of its components is a free
`R`-module. -/
@[stacks 00LQ "termwise free complexes"]
def IsTermwiseFree (K : HomologicalComplex (ModuleCat R) c) : Prop :=
  ∀ i : ι, Module.Free R (K.X i)

/-- A module-valued homological complex is termwise finite when each of its components is a
finite `R`-module. -/
@[stacks 00MS "termwise finite complexes"]
def IsTermwiseFinite (K : HomologicalComplex (ModuleCat R) c) : Prop :=
  ∀ i : ι, Module.Finite R (K.X i)

/-- A module-valued homological complex is termwise finite free when each component is both a
free and a finite `R`-module. -/
@[stacks 064Q "termwise finite free complexes"]
class IsTermwiseFiniteFree (K : HomologicalComplex (ModuleCat R) c) : Prop where
  /-- Every component of the complex is a finite free module. -/
  out : ∀ i : ι, Module.Free R (K.X i) ∧ Module.Finite R (K.X i)

namespace IsTermwiseFiniteFree

variable {K : HomologicalComplex (ModuleCat R) c}

/-- Assemble the finite-free class from the separate termwise freeness and finiteness predicates. -/
@[stacks 064Q "assemble termwise finite freeness"]
theorem of (hfree : K.IsTermwiseFree) (hfinite : K.IsTermwiseFinite) :
    K.IsTermwiseFiniteFree :=
  ⟨fun i => ⟨hfree i, hfinite i⟩⟩

end IsTermwiseFiniteFree

/-- Unfolding the termwise-free predicate exposes the free structure in every degree. -/
@[stacks 00LQ "termwise free characterization"]
theorem isTermwiseFree_iff (K : HomologicalComplex (ModuleCat R) c) :
    K.IsTermwiseFree ↔ ∀ i : ι, Module.Free R (K.X i) := Iff.rfl

/-- Unfolding the termwise-finite predicate exposes the finite structure in every degree. -/
@[stacks 00MS "termwise finite characterization"]
theorem isTermwiseFinite_iff (K : HomologicalComplex (ModuleCat R) c) :
    K.IsTermwiseFinite ↔ ∀ i : ι, Module.Finite R (K.X i) := Iff.rfl

/-- A complex is termwise finite free exactly when it is both termwise free and termwise finite. -/
@[stacks 064Q "termwise finite-free characterization"]
theorem isTermwiseFiniteFree_iff (K : HomologicalComplex (ModuleCat R) c) :
    K.IsTermwiseFiniteFree ↔ K.IsTermwiseFree ∧ K.IsTermwiseFinite :=
  ⟨fun hK => ⟨fun i => (hK.out i).1, fun i => (hK.out i).2⟩,
    fun hK => IsTermwiseFiniteFree.of hK.1 hK.2⟩

/-- A termwise finite free complex supplies the canonical free instance in every degree. -/
@[stacks 064Q "termwise finite-free free instance"]
instance (K : HomologicalComplex (ModuleCat R) c) [hK : K.IsTermwiseFiniteFree] (i : ι) :
    Module.Free R (K.X i) :=
  (hK.out i).1

/-- A termwise finite free complex supplies the canonical finite instance in every degree. -/
@[stacks 064Q "termwise finite-free finite instance"]
instance (K : HomologicalComplex (ModuleCat R) c) [hK : K.IsTermwiseFiniteFree] (i : ι) :
    Module.Finite R (K.X i) :=
  (hK.out i).2

namespace IsTermwiseFree

variable {K : HomologicalComplex (ModuleCat R) c}

/-- A termwise-free complex has a free module in each specified degree. -/
@[stacks 00LQ "termwise free component"]
theorem free (hK : K.IsTermwiseFree) (i : ι) : Module.Free R (K.X i) := hK i

/-- A termwise-free complex has a projective object in each specified degree. -/
@[stacks 00LQ "termwise free projective component"]
theorem projective (hK : K.IsTermwiseFree) (i : ι) : Projective (K.X i) := by
  letI := hK.free i
  infer_instance

/-- A nonzerodivisor acts regularly on every term of a termwise-free complex. -/
@[stacks 00LQ "termwise free regular scalar"]
theorem isTermwiseSMulRegular (hK : K.IsTermwiseFree) {r : R}
    (hr : r ∈ nonZeroDivisors R) : K.IsTermwiseSMulRegular r := by
  intro i
  letI := hK.free i
  exact (isRegular_iff_mem_nonZeroDivisors.mpr hr).isSMulRegular

end IsTermwiseFree

namespace IsTermwiseFinite

variable {K : HomologicalComplex (ModuleCat R) c}

/-- A termwise-finite complex has a finite module in each specified degree. -/
@[stacks 00MS "termwise finite component"]
theorem finite (hK : K.IsTermwiseFinite) (i : ι) : Module.Finite R (K.X i) := hK i

/-- The homology of a termwise finite complex over a Noetherian ring is finite. -/
@[stacks 0AZ4 "finiteness of homology"]
theorem finite_homology [IsNoetherianRing R] (hK : K.IsTermwiseFinite) (i : ι) :
    Module.Finite R ((HomologicalComplex.homologyFunctor (ModuleCat R) c i).obj K) := by
  letI := hK.finite i
  haveI : Module.Finite R (K.cycles i) :=
    Module.Finite.of_injective (K.iCycles i).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  exact Module.Finite.of_surjective (K.homologyπ i).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

end IsTermwiseFinite

namespace IsTermwiseFiniteFree

variable {K : HomologicalComplex (ModuleCat R) c}

/-- A specified term of a termwise finite free complex is free. -/
@[stacks 064Q "termwise finite-free component free"]
theorem free (hK : K.IsTermwiseFiniteFree) (i : ι) : Module.Free R (K.X i) := (hK.out i).1

/-- A specified term of a termwise finite free complex is finite. -/
@[stacks 064Q "termwise finite-free component finite"]
theorem finite (hK : K.IsTermwiseFiniteFree) (i : ι) : Module.Finite R (K.X i) := (hK.out i).2

/-- A termwise finite free complex is termwise free. -/
@[stacks 064Q "finite-free to termwise free"]
theorem isTermwiseFree (hK : K.IsTermwiseFiniteFree) : K.IsTermwiseFree := hK.free

/-- A termwise finite free complex is termwise finite. -/
@[stacks 064Q "finite-free to termwise finite"]
theorem isTermwiseFinite (hK : K.IsTermwiseFiniteFree) : K.IsTermwiseFinite := hK.finite

/-- Every component of a termwise finite free complex is projective. -/
@[stacks 064Q "termwise finite-free projective component"]
theorem projective (hK : K.IsTermwiseFiniteFree) (i : ι) : Projective (K.X i) :=
  hK.isTermwiseFree.projective i

/-- A nonzerodivisor acts regularly on a termwise finite-free complex. -/
@[stacks 064Q "termwise finite-free regular scalar"]
theorem isTermwiseSMulRegular (hK : K.IsTermwiseFiniteFree) {r : R}
    (hr : r ∈ nonZeroDivisors R) : K.IsTermwiseSMulRegular r :=
  hK.isTermwiseFree.isTermwiseSMulRegular hr

/-- Termwise finite freeness transports across a strict isomorphism of complexes. -/
@[stacks 064Q "termwise finite-free transport"]
theorem of_iso (hK : K.IsTermwiseFiniteFree)
    {L : HomologicalComplex (ModuleCat R) c} (e : K ≅ L) : L.IsTermwiseFiniteFree := by
  refine ⟨fun i => ?_⟩
  letI := hK.free i
  letI := hK.finite i
  exact ⟨Module.Free.of_equiv (HomologicalComplex.Hom.isoApp e i).toLinearEquiv,
    Module.Finite.equiv (HomologicalComplex.Hom.isoApp e i).toLinearEquiv⟩

end IsTermwiseFiniteFree

/-- The canonical zero complex is termwise finite free. -/
instance instIsTermwiseFiniteFreeZeroModuleCat :
    (HomologicalComplex.zero : HomologicalComplex (ModuleCat R) c).IsTermwiseFiniteFree := by
  refine ⟨fun i => ?_⟩
  letI : Subsingleton ((HomologicalComplex.zero : HomologicalComplex (ModuleCat R) c).X i) :=
    ModuleCat.subsingleton_of_isZero (Limits.isZero_zero _)
  exact ⟨inferInstance, inferInstance⟩

/-- The biproduct of termwise finite free complexes is termwise finite free. -/
instance instIsTermwiseFiniteFreeBiprodModuleCat (K L : HomologicalComplex (ModuleCat R) c)
    [K.IsTermwiseFiniteFree] [L.IsTermwiseFiniteFree] :
    (K ⊞ L).IsTermwiseFiniteFree := by
  refine ⟨fun i => ?_⟩
  let e := ((biprodXIso K L i) ≪≫ ModuleCat.biprodIsoProd (K.X i) (L.X i)).toLinearEquiv
  exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm⟩

end HomologicalComplex

namespace ChainComplex

variable {R : Type u} [Ring R]

/-- The chain-complex specialization of the shape-independent termwise-free predicate. -/
@[stacks 00LQ "chain-complex termwise free specialization"]
abbrev IsTermwiseFree (F : ChainComplex (ModuleCat R) ℕ) : Prop :=
  HomologicalComplex.IsTermwiseFree F

/-- The chain-complex specialization of the shape-independent termwise-finite predicate. -/
@[stacks 00MS "chain-complex termwise finite specialization"]
abbrev IsTermwiseFinite (F : ChainComplex (ModuleCat R) ℕ) : Prop :=
  HomologicalComplex.IsTermwiseFinite F

/-- The chain-complex specialization of the shape-independent termwise-finite-free class. -/
@[stacks 064Q "chain-complex finite-free specialization"]
abbrev IsTermwiseFiniteFree (F : ChainComplex (ModuleCat R) ℕ) : Prop :=
  HomologicalComplex.IsTermwiseFiniteFree F

end ChainComplex

namespace CochainComplex

variable {R : Type u} [Ring R]

/-- The integer cochain-complex specialization of the shape-independent termwise-free
predicate. -/
@[stacks 00LQ "cochain-complex termwise free specialization"]
abbrev IsTermwiseFree (K : CochainComplex (ModuleCat R) ℤ) : Prop :=
  HomologicalComplex.IsTermwiseFree K

/-- The integer cochain-complex specialization of the shape-independent termwise-finite
predicate. -/
@[stacks 00MS "cochain-complex termwise finite specialization"]
abbrev IsTermwiseFinite (K : CochainComplex (ModuleCat R) ℤ) : Prop :=
  HomologicalComplex.IsTermwiseFinite K

/-- The integer cochain-complex specialization of the shape-independent termwise-finite-free
class. -/
@[stacks 064Q "cochain-complex finite-free specialization"]
abbrev IsTermwiseFiniteFree (K : CochainComplex (ModuleCat R) ℤ) : Prop :=
  HomologicalComplex.IsTermwiseFiniteFree K

namespace IsTermwiseFiniteFree

/-- Compatibility accessor for the finite-free structures in every integer cochain degree. -/
theorem out (E : CochainComplex (ModuleCat R) ℤ) [hE : E.IsTermwiseFiniteFree] (i : ℤ) :
    Module.Free R (E.X i) ∧ Module.Finite R (E.X i) :=
  HomologicalComplex.IsTermwiseFiniteFree.out i

end IsTermwiseFiniteFree

end CochainComplex

namespace CochainComplex.Nat

variable {R : Type u} [Ring R]

/-- The nonnegative cochain-complex specialization of the shape-independent termwise-free
predicate. -/
@[stacks 00LQ "nonnegative cochain termwise free specialization"]
abbrev IsTermwiseFree (K : CochainComplex (ModuleCat R) ℕ) : Prop :=
  HomologicalComplex.IsTermwiseFree K

/-- The nonnegative cochain-complex specialization of the shape-independent termwise-finite
predicate. -/
@[stacks 00MS "nonnegative cochain termwise finite specialization"]
abbrev IsTermwiseFinite (K : CochainComplex (ModuleCat R) ℕ) : Prop :=
  HomologicalComplex.IsTermwiseFinite K

/-- The nonnegative cochain-complex specialization of the shape-independent termwise
finite-free class. -/
@[stacks 064Q "nonnegative cochain finite-free specialization"]
abbrev IsTermwiseFiniteFree (K : CochainComplex (ModuleCat R) ℕ) : Prop :=
  HomologicalComplex.IsTermwiseFiniteFree K

end CochainComplex.Nat
