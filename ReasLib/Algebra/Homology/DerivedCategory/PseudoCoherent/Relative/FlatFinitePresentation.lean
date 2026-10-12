/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Module.FinitePresentation
public import ReasLib.Algebra.Module.Flat.Relative
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Restrict
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Module
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pseudo-coherence of flat finitely presented modules

This is the module-level bridge used when a bounded complex has terms that are flat over a base
and finitely presented over the target algebra.  It is separate from the derived model criterion:
the bridge can be reused degreewise by truncation and Hom-complex arguments.  Its flatness input is
the canonical `Module.FlatAlong` predicate, so callers do not have to expose the implementation
object produced by `ModuleCat.restrictScalars`.

@stack 0DHV
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace CategoryTheory.ModuleCat

/-- Stacks `0DHV`: a module that is flat over a base and finitely presented over the target is pseudo-coherent
over the target. -/
@[stacks 0DHV "flat finite-presentation module is pseudo-coherent"]
theorem IsPseudoCoherent.of_flat_finitePresentation
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    (M : ModuleCat A)
    (hFlat : Module.FlatAlong (algebraMap R A) M)
    (hFP : Module.FinitePresentation A M) :
    M.IsPseudoCoherent := sorry

end CategoryTheory.ModuleCat

end
