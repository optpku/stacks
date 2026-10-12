/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Basic

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- For a scheme morphism `f : X ⟶ S`, the following conditions are equivalent:
`f` is unramified and a monomorphism; `f` is unramified and universally injective;
`f` is locally of finite type and a monomorphism; `f` is universally injective,
locally of finite type, and formally unramified; and `f` is locally of finite type
with every fiber empty or canonically isomorphic to the spectrum of its residue field. -/
theorem tfae_unramified_mono {X S : Scheme.{u}} (f : X ⟶ S) :
    List.TFAE [
      Unramified f ∧ Mono f,
      Unramified f ∧ UniversallyInjective f,
      LocallyOfFiniteType f ∧ Mono f,
      UniversallyInjective f ∧ LocallyOfFiniteType f ∧ FormallyUnramified f,
      LocallyOfFiniteType f ∧
        ∀ s : S, IsEmpty (f.fiber s) ∨ IsIso (f.fiberToSpecResidueField s)] := sorry

end AlgebraicGeometry
