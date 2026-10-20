/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.FinitePresentation
public import ReasLib.Algebra.RingHom.Factorisation
public import ReasLib.RingTheory.RingHom.IndSmooth.Basic

/-!
# A factorization criterion for ind-smooth ring maps

The public hypothesis is map-first.  It hides the common-universe categorical
bookkeeping used by `MorphismProperty.ind`, while retaining every map and
commutative triangle needed by downstream applications.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace RingHom.IndSmooth

variable {R : Type u} {L : Type v} [CommRing R] [CommRing L]

/-- Every finite-presentation test algebra mapping compatibly to the target factors through a
smooth algebra over the source. Test objects live in the common universe used by `IndSmooth`;
arbitrary-universe tests enter through the canonical lifts. -/
def HasFactorisations (f : R →+* L) : Prop :=
  ∀ (A : Type (max u v)) [CommRing A] (a : R →+* A),
    a.FinitePresentation →
      ∀ (g : A →+* L), g.comp a = f →
        ∃ F : g.Factorisation, (F.fromSource.comp a).Smooth

/-- An ind-smooth ring map satisfies the finite-presentation factorisation
criterion. -/
theorem hasFactorisations {f : R →+* L} (h : f.IndSmooth) :
    HasFactorisations f := sorry

/-- Lemma 10.127.4, tag `07C3`: ind-smoothness is equivalent to factorisation
of every finite-presentation test map through a smooth algebra. -/
@[stacks 07C3 "ind-smooth factorisation criterion"]
theorem iff_hasFactorisations (f : R →+* L) :
    f.IndSmooth ↔ HasFactorisations f := sorry

namespace HasFactorisations

/-- The finite-presentation factorization criterion implies that a ring map is a filtered
colimit of smooth ring maps. -/
theorem indSmooth {f : R →+* L} (h : HasFactorisations f) :
    f.IndSmooth := sorry

end HasFactorisations

end RingHom.IndSmooth
