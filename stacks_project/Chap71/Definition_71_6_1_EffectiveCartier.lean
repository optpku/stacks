module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.EffectiveCartier
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
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.IsEffectiveCartierDivisor :
    {S : Scheme.{u}} → {D X : AlgebraicSpace S} → (D ⟶ X) → Prop)

#check
  (AlgebraicGeometry.AlgebraicSpace.isEffectiveCartierDivisor_iff :
    ∀ {S : Scheme.{u}} {D X : AlgebraicSpace S} (i : D ⟶ X),
      IsEffectiveCartierDivisor i ↔
        IsClosedImmersion i ∧ isInvertibleObject (Hom.idealSheaf i))

#check
  (AlgebraicGeometry.AlgebraicSpace.IsEffectiveCartierDivisor.invertibleIdealSheaf :
    ∀ {S : Scheme.{u}} {D X : AlgebraicSpace S} {i : D ⟶ X}
      [IsEffectiveCartierDivisor i], isInvertibleObject (Hom.idealSheaf i))

#check
  (AlgebraicGeometry.AlgebraicSpace.isEffectiveCartierDivisor_top :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S},
      IsEffectiveCartierDivisor
        (ClosedSubspace.ofQuasiCoherentIdeal (⊤ : IdealSubobject X)).ι)

#check
  (AlgebraicGeometry.AlgebraicSpace.IsEffectiveCartierDivisor.isLocallyPrincipal :
    ∀ {S : Scheme.{u}} {D X : AlgebraicSpace S} (i : D ⟶ X)
      [IsEffectiveCartierDivisor i], IsLocallyPrincipal i)

#check
  (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.isEffectiveCartierDivisor_iff :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : ClosedSubspace X),
      IsEffectiveCartierDivisor Z.ι ↔ isInvertibleObject (Hom.idealSheaf Z.ι))
