/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent
public import ReasLib.RingTheory.RingHom.Perfect.Flat

/-!
# Pseudo-coherence of flat finitely presented scheme morphisms
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A flat scheme morphism that is locally of finite presentation is pseudo-coherent. -/
instance pseudoCoherent_of_flat_of_locallyOfFinitePresentation
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] :
    PseudoCoherent f := sorry

end AlgebraicGeometry
