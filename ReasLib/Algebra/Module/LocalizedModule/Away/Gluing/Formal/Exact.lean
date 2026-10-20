module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Formal.OfModule
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exactness properties of formal gluing

For a flat ring map, the formal-gluing category is abelian, canonical formal gluing is exact,
and canonical formal gluing preserves colimits.

@stack 05EN
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u v w

noncomputable section

namespace LocalizedModule.Away.FormalGluing

variable {R S : Type u} [CommRing R] [CommRing S]
variable {ι : Type w}

/-- Lemma 15.90.13 (1): formal gluing along a flat ring map is an abelian category. -/
@[stacks 05EN "(1) formal gluing is abelian"]
theorem existsAbelian_of_flat (φ : R →+* S) (f : ι → R) (hflat : φ.Flat) :
    Nonempty (Abelian (FormalGluing.{u, v, w} φ f)) := sorry

/-- Lemma 15.90.13 (2): canonical formal gluing along a flat ring map is exact for a suitable
abelian structure on the formal-gluing category. -/
@[stacks 05EN "(2) exactness of canonical formal gluing"]
theorem existsExactOfModule_of_flat (φ : R →+* S) (f : ι → R) (hflat : φ.Flat) :
    ∃ h : Abelian (FormalGluing.{u, v, w} φ f),
      letI := h
      exactFunctor (ModuleCat.{max u v} R) (FormalGluing.{u, v, w} φ f)
        (ofModuleFunctor.{u, v, w} φ f) := sorry

/-- Lemma 15.90.13 (3): canonical formal gluing along a flat ring map preserves all colimits. -/
@[stacks 05EN "(3) canonical formal gluing preserves colimits"]
theorem ofModule_preservesColimits_of_flat (φ : R →+* S) (f : ι → R)
    (hflat : φ.Flat) :
    PreservesColimits (ofModuleFunctor.{u, v, w} φ f) := sorry

end LocalizedModule.Away.FormalGluing
