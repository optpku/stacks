module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.StructureSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 36.32.6 (1): the canonical map `𝒪_S ⟶ f_*𝒪_X` is an isomorphism. -/
@[stacks 0E0L] #check
  (AlgebraicGeometry.Scheme.Hom.StructureSheaf.isIso_of_geometricallyReduced_geometricallyConnected :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
      [GeometricallyReduced f] [GeometricallyConnected f],
      IsIso (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom))

/- Lemma 36.32.6 (2): the canonical map remains an isomorphism after every base change. -/
@[stacks 0E0L] #check
  (AlgebraicGeometry.Scheme.Hom.StructureSheaf.baseChange_isIso_of_geometricallyReduced_geometricallyConnected :
    ∀ {X S S' : Scheme.{u}} (f : X ⟶ S)
      [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
      [GeometricallyReduced f] [GeometricallyConnected f]
      (g : S' ⟶ S),
      IsIso
        (RingedSpace.Hom.commRingSheafPushforwardMap (pullback.snd f g).toShHom))
