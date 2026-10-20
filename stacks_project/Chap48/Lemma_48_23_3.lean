module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.CohenMacaulay
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.RingedSpace.ModuleDerived

universe u

/- Lemma 48.23.3: for a flat morphism `f : X ⟶ Y` in `FiniteTypeSeparatedOver S`,
the morphism is Cohen–Macaulay at `x` if and only if the compactification model
of `f⁺!𝒪_Y` is concentrated in one degree on an open neighborhood of `x`. -/
@[stacks 0C0Z] #check
  (AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek.cohenMacaulayAt_iff_isLocallyConcentratedAt :
    ∀ {S : Scheme.{u}} [IsNoetherian S]
      {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y) [Flat f.hom.left]
      (P : AlgebraicGeometry.Scheme.Compactification.Of Y.obj.left
        (Over.mk f.hom.left))
      (A : DerivedQCoh.PlusRightAdjoint
        (AlgebraicGeometry.Scheme.Compactification.Of.ambientMorphism P))
      (x : X.obj.left),
      AlgebraicGeometry.Scheme.Hom.CohenMacaulayAt f.hom.left x ↔
        AlgebraicGeometry.RingedSpace.ModuleDerived.IsLocallyConcentratedAt
          (AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek.dualizingObject
            f P A).obj x)
