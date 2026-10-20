module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Fixed.Termwise.Plus
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Source-Facing Predicates for Bounded-Below Replacements

This file retains the elementary predicates used by source statements about bounded-below
replacements.  Canonical resolution objects and bridges to these predicates live in separate
leaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe v u

namespace CochainComplex

section

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [CategoryWithHomology A]

namespace Plus.TermsIn

/-- A morphism `α : K ⟶ I` whose target is zero strictly below `a` and has every term in `P`. -/
@[stacks 05T6 "bounded-below termwise replacement predicate"]
structure Bounded
    (P : ObjectProperty A) (a : ℤ) (K I : CochainComplex A ℤ) (α : K ⟶ I) : Prop where
  /-- The target complex vanishes strictly below `a`. -/
  strictlyGE : I.IsStrictlyGE a
  /-- Every term of the target complex lies in `P`. -/
  term_mem (n : ℤ) : P (I.X n)

namespace Bounded

variable {P : ObjectProperty A} {a : ℤ} {K I : CochainComplex A ℤ} {α : K ⟶ I}

/-- Package the target of a bounded-below termwise replacement with its specified cutoff. -/
abbrev toStrictlyGE (h : Bounded P a K I α) :
    CochainComplex.StrictlyGE.TermsIn P a :=
  ⟨I, ⟨h.strictlyGE, h.term_mem⟩⟩

/-- Package the target of a bounded-below termwise replacement in `Plus.TermsIn P`. -/
abbrev toPlus (h : Bounded P a K I α) : CochainComplex.Plus.TermsIn P :=
  (CochainComplex.StrictlyGE.TermsIn.forgetBound P a).obj h.toStrictlyGE

/-- A bounded-below termwise-`P` comparison morphism that is monomorphic in every degree. -/
@[stacks 05T6 "termwise-monomorphic bounded-below replacement predicate"]
structure Mono
    (P : ObjectProperty A) (a : ℤ) (K I : CochainComplex A ℤ) (α : K ⟶ I) : Prop extends
    Bounded P a K I α where
  /-- The comparison morphism is monomorphic in degree `n`. -/
  term_mono (n : ℤ) : _root_.CategoryTheory.Mono (α.f n)

namespace Mono

/-- A termwise-monomorphic morphism of cochain complexes is monomorphic. -/
theorem mono (h : Bounded.Mono P a K I α) : _root_.CategoryTheory.Mono α := sorry

/-- Package the target of a bounded-below termwise-monomorphic replacement. -/
abbrev toStrictlyGE (h : Bounded.Mono P a K I α) :
    CochainComplex.StrictlyGE.TermsIn P a :=
  h.toBounded.toStrictlyGE

/-- Package the target of a bounded-below termwise-monomorphic replacement after forgetting
the specified cutoff. -/
abbrev toPlus (h : Bounded.Mono P a K I α) : CochainComplex.Plus.TermsIn P :=
  (CochainComplex.StrictlyGE.TermsIn.forgetBound P a).obj h.toStrictlyGE

end Mono

/-- A quasi-isomorphism `K ⟶ I` whose target is bounded below and termwise satisfies `P`. -/
@[stacks 05T6 "quasi-isomorphic bounded-below replacement predicate"]
structure QuasiIso
    (P : ObjectProperty A) (a : ℤ) (K I : CochainComplex A ℤ) (α : K ⟶ I) : Prop extends
    Bounded P a K I α where
  /-- The comparison morphism is a quasi-isomorphism. -/
  quasiIso : _root_.QuasiIso α

namespace QuasiIso

/-- Package the target of a bounded-below quasi-isomorphic replacement. -/
abbrev toStrictlyGE (h : Bounded.QuasiIso P a K I α) :
    CochainComplex.StrictlyGE.TermsIn P a :=
  h.toBounded.toStrictlyGE

/-- Package the target of a bounded-below quasi-isomorphic replacement after forgetting the
specified cutoff. -/
abbrev toPlus (h : Bounded.QuasiIso P a K I α) : CochainComplex.Plus.TermsIn P :=
  (CochainComplex.StrictlyGE.TermsIn.forgetBound P a).obj h.toStrictlyGE

/-- A bounded-below termwise-`P` quasi-isomorphic replacement that is monomorphic in every
degree. -/
@[stacks 05T6 "termwise-monomorphic quasi-isomorphic bounded-below replacement predicate"]
structure Mono
    (P : ObjectProperty A) (a : ℤ) (K I : CochainComplex A ℤ) (α : K ⟶ I) : Prop extends
    Bounded.QuasiIso P a K I α where
  /-- The comparison morphism is monomorphic in degree `n`. -/
  term_mono (n : ℤ) : _root_.CategoryTheory.Mono (α.f n)

namespace Mono

/-- Forgetting quasi-isomorphism data keeps the primitive termwise-monomorphic replacement
data. -/
abbrev toMono (h : Bounded.QuasiIso.Mono P a K I α) : Bounded.Mono P a K I α where
  toBounded := h.toQuasiIso.toBounded
  term_mono := h.term_mono

/-- A termwise-monomorphic quasi-isomorphic replacement map is monomorphic. -/
theorem mono (h : Bounded.QuasiIso.Mono P a K I α) :
    _root_.CategoryTheory.Mono α := sorry

/-- Package the target of a termwise-monomorphic replacement in `Plus.TermsIn P`. -/
abbrev toStrictlyGE (h : Bounded.QuasiIso.Mono P a K I α) :
    CochainComplex.StrictlyGE.TermsIn P a :=
  h.toQuasiIso.toStrictlyGE

/-- Package the target of a termwise-monomorphic replacement after forgetting the specified
cutoff. -/
abbrev toPlus (h : Bounded.QuasiIso.Mono P a K I α) :
    CochainComplex.Plus.TermsIn P :=
  (CochainComplex.StrictlyGE.TermsIn.forgetBound P a).obj h.toStrictlyGE

end Mono

end QuasiIso

end Bounded

end Plus.TermsIn

end


end CochainComplex

