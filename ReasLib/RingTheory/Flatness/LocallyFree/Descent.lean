/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import ReasLib.RingTheory.Flat.FaithfullyFlat.Projective
public import ReasLib.RingTheory.Flatness.LocallyFree

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Module.LocallyFree

/-- Local freeness of modules does not descend along arbitrary faithfully flat ring maps,
even for projective modules that are countable internal direct sums of finite locally free
modules of rank one and become free after base change. -/
theorem not_fpqcLocal :
    ¬ ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B]
        (M : Type w) [AddCommGroup M] [Module A M] (L : ℕ → Submodule A M),
      Module.Projective A M →
      iSupIndep L →
      iSup L = ⊤ →
      (∀ n, Module.FiniteLocallyFreeOfRank A (L n) 1) →
      (algebraMap A B).FaithfullyFlat →
      Module.Free B (B ⊗[A] M) →
      Module.LocallyFree A M := sorry

/-- Over a Noetherian ring, a module that becomes free after a faithfully flat base change
of finite presentation is locally free. -/
theorem of_fppfFreeBaseChange
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    {M : Type w} [AddCommGroup M] [Module A M] [IsNoetherianRing A]
    (hff : (algebraMap A B).FaithfullyFlat)
    (hfp : (algebraMap A B).FinitePresentation)
    (hfree : Module.Free B (B ⊗[A] M)) :
    Module.LocallyFree A M := sorry

end Module.LocallyFree
