/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Ring.Instances
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Monomorphisms between affine schemes

This leaf keeps the reusable variance bridge from epimorphisms of commutative rings to
monomorphisms of their affine spectra.  The bridge is a named theorem rather than a global
instance, so callers opt in without making typeclass search explore every `Spec.map`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Spec

/-- The contravariant affine-spectrum map sends an epimorphism of commutative rings to a
monomorphism of schemes. -/
@[stacks 01L9 "epi-to-mono variance for affine spectra"]
theorem map_mono_of_epi {R S : CommRingCat.{u}} (f : R ⟶ S) [Epi f] :
    Mono (Spec.map f) := sorry

end AlgebraicGeometry.Spec
