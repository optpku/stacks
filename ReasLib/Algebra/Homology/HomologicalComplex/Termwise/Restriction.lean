/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.Algebra.Module.Flat.Relative
public import ReasLib.Algebra.Homology.HomologicalComplex.Flat.ModuleCat
public import ReasLib.Algebra.Homology.HomologicalComplex.Restriction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Termwise properties after restriction of scalars

This leaf records relative termwise flatness along an explicit ring map.  The concrete restricted
complex is owned by `HomologicalComplex.Restriction`; algebra-specialized declarations here are
abbreviations at `algebraMap`.
@stack 0E1U
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory

namespace HomologicalComplex

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]
variable {ι : Type w} {c : ComplexShape ι}

/-- Stacks `0E1U`: a complex of `A`-modules is termwise flat along `σ : R →+* A` when its restriction to
`R` is termwise flat. -/
@[stacks 0E1U "termwise flatness along a ring map"]
def IsTermwiseFlatAlong
    (K : HomologicalComplex (ModuleCat A) c) (σ : R →+* A) : Prop :=
  ∀ i : ι, Module.FlatAlong σ (K.X i)

/-- Stacks `0E1U`: relative termwise flatness is flatness of every restricted component. -/
@[stacks 0E1U "degreewise relative flatness criterion"]
theorem isTermwiseFlatAlong_iff_moduleFlat
    (K : HomologicalComplex (ModuleCat A) c) (σ : R →+* A) :
    K.IsTermwiseFlatAlong σ ↔
      ∀ i : ι, Module.Flat R ((ModuleCat.restrictScalars σ).obj (K.X i)) := sorry
/- Proof strategy: unfold `IsTermwiseFlatAlong`; the statement is the degreewise module-flatness
criterion for the restricted components. -/

namespace IsTermwiseFlatAlong

variable {σ : R →+* A} {K : HomologicalComplex (ModuleCat A) c}

/-- Stacks `0E1U`: every component of a relatively termwise-flat complex is flat along the
specified ring homomorphism in the canonical module-level sense. -/
@[stacks 0E1U "canonical relative flat components"]
theorem flatAlong (hK : K.IsTermwiseFlatAlong σ) (i : ι) :
    Module.FlatAlong σ (K.X i) := sorry

/-- Stacks `0E1U`: every restricted component of a relatively termwise-flat complex is flat. -/
@[stacks 0E1U "flat restricted components"]
theorem moduleFlat (hK : K.IsTermwiseFlatAlong σ) (i : ι) :
    Module.Flat R ((ModuleCat.restrictScalars σ).obj (K.X i)) := sorry
/- Proof strategy: specialize `hK` at degree `i`. -/

end IsTermwiseFlatAlong

/-- Stacks `0E1U`: a complex of modules over an `R`-algebra is termwise flat over `R` when restriction along
`algebraMap R A` is termwise flat. -/
@[stacks 0E1U "termwise flatness over a base algebra"]
abbrev IsTermwiseFlatOver
    (R : Type u) [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    (K : HomologicalComplex (ModuleCat A) c) : Prop :=
  K.IsTermwiseFlatAlong (algebraMap R A)

namespace IsTermwiseFlat

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]
variable {K : HomologicalComplex (ModuleCat A) c}

/-- Stacks `0E1U`: a termwise-flat complex remains termwise flat after restriction along a flat
ring homomorphism. -/
@[stacks 0E1U "termwise flatness along a flat ring map"]
theorem along (hK : K.IsTermwiseFlat) (σ : R →+* A) (hσ : σ.Flat) :
    K.IsTermwiseFlatAlong σ := sorry

/-- Stacks `0E1U`: a termwise-flat `A`-complex is termwise flat over a flat base algebra `R`. -/
@[stacks 0E1U "termwise flatness over a flat algebra"]
theorem over [Algebra R A] [Module.Flat R A] (hK : K.IsTermwiseFlat) :
    HomologicalComplex.IsTermwiseFlatOver (A := A) R K := sorry

end IsTermwiseFlat

end HomologicalComplex

namespace HomologicalComplex

variable {R A : Type u} [CommRing R] [CommRing A]
variable {ι : Type w} {c : ComplexShape ι}

/-- Stacks `0E1U`: in the universe supported by the canonical monoidal structure on `ModuleCat`,
the relative predicate is categorical termwise flatness of the explicitly restricted complex. -/
@[simp, stacks 0E1U "termwise flatness of a restricted complex"]
theorem isTermwiseFlat_restrictScalarsAlong_iff
    (K : HomologicalComplex (ModuleCat A) c) (σ : R →+* A) :
    IsTermwiseFlat (K.restrictScalarsAlong σ) ↔ K.IsTermwiseFlatAlong σ := sorry

end HomologicalComplex

namespace CochainComplex

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]

/-- Stacks `0E1U`: the integer cochain-complex specialization of relative termwise flatness along a ring map. -/
@[stacks 0E1U "cochain-complex relative termwise flatness"]
abbrev IsTermwiseFlatAlong
    (K : CochainComplex (ModuleCat A) ℤ) (σ : R →+* A) : Prop :=
  HomologicalComplex.IsTermwiseFlatAlong K σ

/-- Stacks `0E1U`: the integer cochain-complex specialization of termwise flatness over a base algebra. -/
@[stacks 0E1U "cochain-complex termwise flatness over a base"]
abbrev IsTermwiseFlatOver
    (R : Type u) [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    (K : CochainComplex (ModuleCat A) ℤ) : Prop :=
  HomologicalComplex.IsTermwiseFlatOver R K

end CochainComplex
