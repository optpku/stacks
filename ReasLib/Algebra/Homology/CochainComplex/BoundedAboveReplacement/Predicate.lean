module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Fixed.Termwise.Minus
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Source-Facing Predicates for Bounded-Above Replacements

This file retains the elementary predicates used by source statements about bounded-above
replacements.  Canonical resolution objects and bridges to these predicates live in separate
leaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe v u

namespace CochainComplex

section

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [CategoryWithHomology A]

namespace Minus.TermsIn

/-- A morphism `α : Q ⟶ K` whose source is zero strictly above `a` and has every term in `P`. -/
@[stacks 05T7 "bounded-above termwise replacement predicate"]
structure Bounded
    (P : ObjectProperty A) (a : ℤ) (K Q : CochainComplex A ℤ) (α : Q ⟶ K) : Prop where
  /-- The resolving complex vanishes strictly above `a`. -/
  strictlyLE : Q.IsStrictlyLE a
  /-- Every term of the resolving complex lies in `P`. -/
  term_mem (n : ℤ) : P (Q.X n)

namespace Bounded

variable {P : ObjectProperty A} {a : ℤ} {K Q : CochainComplex A ℤ} {α : Q ⟶ K}

/-- Package the source of a bounded-above termwise replacement with its specified cutoff. -/
abbrev toStrictlyLE (h : Bounded P a K Q α) :
    CochainComplex.StrictlyLE.TermsIn P a :=
  ⟨Q, ⟨h.strictlyLE, h.term_mem⟩⟩

/-- Package the resolving complex of a bounded-above termwise replacement in
`CochainComplex.Minus.TermsIn P`. -/
abbrev toMinus (h : Bounded P a K Q α) : CochainComplex.Minus.TermsIn P :=
  (CochainComplex.StrictlyLE.TermsIn.forgetBound P a).obj h.toStrictlyLE

/-- A bounded-above termwise-`P` comparison morphism that is a quasi-isomorphism. -/
@[stacks 05T7 "quasi-isomorphic bounded-above replacement predicate"]
structure QuasiIso
    (P : ObjectProperty A) (a : ℤ) (K Q : CochainComplex A ℤ) (α : Q ⟶ K) : Prop extends
    Bounded P a K Q α where
  /-- The comparison morphism is a quasi-isomorphism. -/
  quasiIso : _root_.QuasiIso α

namespace QuasiIso

/-- Package the resolving complex of a bounded-above quasi-isomorphic replacement. -/
abbrev toStrictlyLE (h : Bounded.QuasiIso P a K Q α) :
    CochainComplex.StrictlyLE.TermsIn P a :=
  h.toBounded.toStrictlyLE

/-- Package the resolving complex of a bounded-above quasi-isomorphic replacement after
forgetting the specified cutoff. -/
abbrev toMinus (h : Bounded.QuasiIso P a K Q α) : CochainComplex.Minus.TermsIn P :=
  (CochainComplex.StrictlyLE.TermsIn.forgetBound P a).obj h.toStrictlyLE

/-- A bounded-above termwise-`P` quasi-isomorphic replacement whose comparison morphism is
epimorphic in every degree. -/
@[stacks 05T7 "termwise-epimorphic quasi-isomorphic bounded-above replacement predicate"]
structure Epi
    (P : ObjectProperty A) (a : ℤ) (K Q : CochainComplex A ℤ) (α : Q ⟶ K) : Prop extends
    Bounded.QuasiIso P a K Q α where
  /-- The comparison morphism is epimorphic in degree `n`. -/
  term_epi (n : ℤ) : _root_.CategoryTheory.Epi (α.f n)

namespace Epi

/-- A termwise-epimorphic morphism of cochain complexes is epimorphic as a morphism of
complexes. -/
theorem epi (h : Bounded.QuasiIso.Epi P a K Q α) :
    _root_.CategoryTheory.Epi α := sorry

/-- Package the resolving complex of a termwise-epimorphic replacement in
`CochainComplex.Minus.TermsIn P`. -/
abbrev toStrictlyLE (h : Bounded.QuasiIso.Epi P a K Q α) :
    CochainComplex.StrictlyLE.TermsIn P a :=
  h.toQuasiIso.toStrictlyLE

/-- Package the resolving complex of a termwise-epimorphic replacement after forgetting the
specified cutoff. -/
abbrev toMinus (h : Bounded.QuasiIso.Epi P a K Q α) :
    CochainComplex.Minus.TermsIn P :=
  (CochainComplex.StrictlyLE.TermsIn.forgetBound P a).obj h.toStrictlyLE

end Epi

end QuasiIso

end Bounded

end Minus.TermsIn

end


end CochainComplex

