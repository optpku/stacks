module

public import ReasLib.AlgebraicGeometry.Scheme.Module.DescentLocus.Closed
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 37.33.4: let `f : X ⟶ S` and `E` be as in Lemma 37.33.1, with `E`
invertible. If the geometric fibers of `f` are integral, then the finitely presented
immersion `j : Z ⟶ S` representing the descent locus is a closed immersion. -/
@[stacks 0BF0] #check (
  AlgebraicGeometry.Scheme.Modules.RepresentsDescentLocus.isClosedImmersion :
    ∀ {X S Z : Scheme.{u}} (f : X ⟶ S)
      [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
      [GeometricallyIntegral f]
      (E : X.Modules) [E.IsFiniteLocallyFree] [Invertible E]
      (_ : ∀ {T : Scheme.{u}} (g : T ⟶ S),
        IsIso (SheafOfModules.unitToPushforwardObjUnit
          (pullback.snd f g).toRingCatSheafHom))
      (j : Z ⟶ S) [IsImmersion j] [Scheme.Hom.FinitePresentation j]
      (_ : RepresentsDescentLocus f E j),
      IsClosedImmersion j)

end AlgebraicGeometry.Scheme.Modules
