module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Module.DescentLocus
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
import ReasLib.AlgebraicGeometry.Scheme.GlobalSections.Proper
import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.ValuationRing
import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage.Valuation

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules.RepresentsDescentLocus

/-- A finitely presented immersion representing the descent locus of an invertible finite locally
free module along a flat proper finitely presented morphism with geometrically integral fibers is
a closed immersion, provided the structure-sheaf unit is an isomorphism after every base change. -/
theorem isClosedImmersion {X S Z : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
    [GeometricallyIntegral f]
    (E : X.Modules) [E.IsFiniteLocallyFree] [Invertible E]
    (h_unit : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      IsIso (SheafOfModules.unitToPushforwardObjUnit
        (pullback.snd f g).toRingCatSheafHom))
    (j : Z ⟶ S) [IsImmersion j] [Scheme.Hom.FinitePresentation j]
    (hZ : RepresentsDescentLocus f E j) :
    IsClosedImmersion j := sorry

end AlgebraicGeometry.Scheme.Modules.RepresentsDescentLocus
