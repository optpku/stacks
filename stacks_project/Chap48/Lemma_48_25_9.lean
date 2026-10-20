module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Gorenstein.BaseChange
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y Y' : Scheme.{u}}

#check
  (AlgebraicGeometry.Scheme.Hom.gorensteinAt_iff_of_pullback_snd :
    ∀ {X Y Y' : Scheme.{u}} (f : X ⟶ Y) [Flat f] [LocallyOfFiniteType f]
      (g : Y' ⟶ Y) (x' : (pullback f g : Scheme)),
      (pullback.snd f g).gorensteinAt x' ↔
        f.gorensteinAt ((pullback.fst f g) x'))

/- Lemma 48.25.9: For a flat, locally finite-type morphism, the Gorenstein locus
commutes with arbitrary base change. -/
@[stacks 0E0Q] #check
  (AlgebraicGeometry.Scheme.Hom.gorensteinLocus_pullback_snd :
    ∀ {X Y Y' : Scheme.{u}} (f : X ⟶ Y) [Flat f] [LocallyOfFiniteType f]
      (g : Y' ⟶ Y),
      (pullback.snd f g).gorensteinLocus =
        (pullback.fst f g) ⁻¹' f.gorensteinLocus)

end AlgebraicGeometry.Scheme.Hom
