module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Relative.Jacobson
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 37.71.3: a pseudo-coherent derived module for a proper, flat,
finitely presented morphism to `Spec R` is perfect over `Spec R` if its derived
pullback to `Spec (R ⧸ I)` is perfect and `I ≤ Ring.jacobson R`. -/
@[stacks 0DJZ] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.isPerfectOver_of_quotient_of_le_jacobson :
    ∀ (R : CommRingCat.{u}) (I : Ideal R) (_ : I ≤ Ring.jacobson R)
      {X : Scheme.{u}} (f : X ⟶ Spec R)
      [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
      (E : RingedSpace.ModuleDerived X.toRingedSpace)
      (_ : RingedSpace.ModuleDerived.IsPseudoCoherent E)
      (_ : RingedSpace.ModuleDerived.IsPerfectOver
        (pullback.snd f (Spec.quotientMap I)).toShHom
        ((RingedSpace.modulePullbackDerived
          (pullback.fst f (Spec.quotientMap I)).toShHom).obj E)),
      RingedSpace.ModuleDerived.IsPerfectOver f.toShHom E)
