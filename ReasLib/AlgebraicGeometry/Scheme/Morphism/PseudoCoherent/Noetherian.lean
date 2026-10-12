/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent
public import ReasLib.RingTheory.RingHom.PseudoCoherent.Noetherian

/-!
# Pseudo-coherent morphisms over locally Noetherian schemes
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.PseudoCoherent

/-- A scheme morphism to a locally Noetherian scheme is pseudo-coherent if and only if it is
locally of finite type. -/
theorem iff_locallyOfFiniteType {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S] :
    PseudoCoherent f ↔ LocallyOfFiniteType f := sorry

/-- A closed immersion into a locally Noetherian scheme is pseudo-coherent. -/
instance closedImmersion_of_isLocallyNoetherian {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsLocallyNoetherian X] [IsClosedImmersion i] : PseudoCoherent i := sorry

/-- A finite morphism into a locally Noetherian scheme is pseudo-coherent. -/
instance finite_of_isLocallyNoetherian {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [IsFinite f] : PseudoCoherent f := sorry

end AlgebraicGeometry.PseudoCoherent
