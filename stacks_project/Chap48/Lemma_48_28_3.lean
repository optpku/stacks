module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Relative.Homothety
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 48.28.3: for a flat locally finitely presented scheme morphism, the canonical
homothety from the tensor unit to the derived internal endomorphism object of a relative
dualizing complex is invertible. -/
@[stacks 0E2V] #check
  (AlgebraicGeometry.Scheme.RelativeDualizingComplex.homothetyIsIso :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [Flat f] [LocallyOfFinitePresentation f]
      (W : (pullback f f).Opens) (δ : X ⟶ W.toScheme) [IsClosedImmersion δ]
      (hδ : δ ≫ W.ι = pullback.diagonal f)
      [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
      [MonoidalCategory (RingedSpace.ModuleDerived W.toScheme.toRingedSpace)]
      [(RingedSpace.moduleDerivedPushforward δ.toShHom).LaxMonoidal]
      (H_W : MonoidalClosed (RingedSpace.ModuleDerived W.toScheme.toRingedSpace))
      (C : Scheme.RelativeDualizingComplex f W δ hδ H_W)
      (H_X : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)),
      IsIso (@MonoidalClosed.curry' (RingedSpace.ModuleDerived X.toRingedSpace) _ _
        C.complex C.complex (H_X.closed C.complex) (𝟙 C.complex)))
