module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.RingHom.QuasiFinite
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Quasi-Finite Factorizations of Faithfully Flat Maps

This leaf owns the map-level factorization theorem independently of the
particular noetherian approximation and fiber-locus arguments used to prove
it.  The conclusion remains in the canonical ring-hom predicates, so it can
be used without choosing algebra structures.
-/

universe u v w

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A quasi-finite, faithfully flat, finitely presented refinement of a ring
homomorphism. The target universe is independent of the source and target
universes of the original map. -/
@[stacks 034Z "quasi-finite refinement of a faithfully flat map"]
structure QuasiFiniteRefinement (f : R →+* S) where
  /-- The target ring of the refinement. -/
  target : Type w
  /-- The commutative-ring structure on the refinement target. -/
  instCommRing : CommRing target
  /-- The map from the original target to the refinement target. -/
  toTarget : S →+* target
  /-- The composite from the original source is quasi-finite. -/
  quasiFinite : (toTarget.comp f).QuasiFinite
  /-- The composite from the original source is faithfully flat. -/
  faithfullyFlat : (toTarget.comp f).FaithfullyFlat
  /-- The composite from the original source is finitely presented. -/
  finitePresentation : (toTarget.comp f).FinitePresentation

attribute [instance] QuasiFiniteRefinement.instCommRing

namespace QuasiFiniteRefinement

variable {f : R →+* S}

/-- Build a quasi-finite factorization from an explicit target, map, and the
three properties of the composite. -/
@[stacks 034Z "quasi-finite factorization constructor"]
def of {T : Type w} [CommRing T] (g : S →+* T)
    (hqf : (g.comp f).QuasiFinite)
    (hff : (g.comp f).FaithfullyFlat)
    (hfp : (g.comp f).FinitePresentation) :
    QuasiFiniteRefinement f where
  target := T
  instCommRing := inferInstance
  toTarget := g
  quasiFinite := hqf
  faithfullyFlat := hff
  finitePresentation := hfp

/-- The three defining properties of a quasi-finite factorization, exposed as
the source-semantic bundle for consumers that need them together. -/
@[stacks 034Z "quasi-finite refinement specification"]
theorem spec (F : QuasiFiniteRefinement f) :
    (F.toTarget.comp f).QuasiFinite ∧ (F.toTarget.comp f).FaithfullyFlat ∧
      (F.toTarget.comp f).FinitePresentation :=
  ⟨F.quasiFinite, F.faithfullyFlat, F.finitePresentation⟩

end QuasiFiniteRefinement

namespace FaithfullyFlat

/-- Lemma 10.168.10, tag `034Z`: a faithfully flat finitely presented map
admits a quasi-finite refinement with faithfully flat, finitely presented
composite. -/
@[stacks 034Z "quasi-finite refinement of a faithfully flat map"]
theorem exists_quasiFiniteRefinement
    (f : R →+* S) (hff : f.FaithfullyFlat) (hfp : f.FinitePresentation) :
    Nonempty (QuasiFiniteRefinement.{u, v, max u v} f) := sorry

end FaithfullyFlat

end RingHom
