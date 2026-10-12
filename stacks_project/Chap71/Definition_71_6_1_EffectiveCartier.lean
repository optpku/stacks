/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Monoidal.Invertible
public import stacks_project.Chap67.Lemma_67_13_1_Correspondence
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal
public import stacks_project.Chap71.Definition_71_6_1_LocallyPrincipal

/-!
# Effective Cartier divisors on algebraic spaces

A closed immersion of algebraic spaces is an effective Cartier divisor when its
associated ideal sheaf is an invertible module on the small étale site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces is an effective Cartier divisor when it is a closed
immersion whose associated ideal sheaf is an invertible `𝒪_X`-module. -/
class IsEffectiveCartierDivisor {S : Scheme.{u}} {D X : AlgebraicSpace S}
    (i : D ⟶ X) : Prop extends IsClosedImmersion i where
  /-- The associated ideal sheaf is tensor-invertible. -/
  invertibleIdealSheaf : isInvertibleObject (Hom.idealSheaf i)

/-- Effective Cartier unfolds as a closed immersion whose ideal sheaf is invertible. -/
theorem isEffectiveCartierDivisor_iff {S : Scheme.{u}} {D X : AlgebraicSpace S}
    (i : D ⟶ X) :
    IsEffectiveCartierDivisor i ↔
      IsClosedImmersion i ∧ isInvertibleObject (Hom.idealSheaf i) :=
  sorry

/-- An effective Cartier divisor supplies invertibility of its ideal sheaf to typeclass
search. -/
instance instIsInvertibleObject_idealSheaf {S : Scheme.{u}} {D X : AlgebraicSpace S}
    (i : D ⟶ X) [h : IsEffectiveCartierDivisor i] :
    isInvertibleObject (Hom.idealSheaf i) :=
  h.invertibleIdealSheaf

/-- The empty closed subspace, cut out by the unit ideal, is an effective Cartier
divisor. -/
instance instIsEffectiveCartierDivisor_top {S : Scheme.{u}} {X : AlgebraicSpace S} :
    IsEffectiveCartierDivisor
      (ClosedSubspace.ofQuasiCoherentIdeal (⊤ : IdealSubobject X)).ι :=
  sorry

/-- Every effective Cartier divisor is a locally principal closed subspace. -/
instance instIsLocallyPrincipalClosedSubspace_of_isEffectiveCartierDivisor
    {S : Scheme.{u}} {D X : AlgebraicSpace S} (i : D ⟶ X)
    [IsEffectiveCartierDivisor i] : IsLocallyPrincipalClosedSubspace i :=
  sorry

namespace ClosedSubspace

/-- A closed subspace is an effective Cartier divisor exactly when the ideal sheaf of
its inclusion is an invertible `𝒪_X`-module. -/
theorem isEffectiveCartierDivisor_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) :
    IsEffectiveCartierDivisor Z.ι ↔ isInvertibleObject (Hom.idealSheaf Z.ι) :=
  sorry

end ClosedSubspace

end AlgebraicGeometry.AlgebraicSpace
