module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.BaseChange
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 29.35.15: the unramified locus of a locally finite-type morphism commutes with
arbitrary base change; for a locally finite-presentation morphism, so does the G-unramified
locus. -/
@[stacks 0475] #check
  (AlgebraicGeometry.Scheme.Hom.unramifiedAt_locus_pullback_snd :
    ∀ {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f],
      {x' : (pullback f g : Scheme) | (pullback.snd f g).UnramifiedAt x'} =
        (pullback.fst f g) ⁻¹' {x : X | f.UnramifiedAt x})

#check
  (AlgebraicGeometry.Scheme.Hom.gUnramifiedAt_locus_pullback_snd :
    ∀ {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
      [LocallyOfFinitePresentation f],
      {x' : (pullback f g : Scheme) | (pullback.snd f g).GUnramifiedAt x'} =
        (pullback.fst f g) ⁻¹' {x : X | f.GUnramifiedAt x})
