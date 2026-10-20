module

public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.CoherentVanishing
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

universe u

/- Lemma 30.20.9: let `f : X ⟶ Y` be a morphism of schemes and let `y` be a
point of `Y`. Assume `Y` is locally Noetherian, `f` is proper, and
`topologicalKrullDim (f.fiber y) = d`. Then for any coherent `𝒪_X`-module `F`
and every `p` with `d < p`, the stalk of `R^p f_* F` at `y` vanishes. -/
@[stacks 02V7] #check
  (AlgebraicGeometry.Scheme.higherDirectImageModule_stalk_isZero_of_proper_fiberDimension :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian Y]
      (f : X ⟶ Y) [AlgebraicGeometry.IsProper f] (y : Y) (d : WithBot ℕ∞)
      (hdim : topologicalKrullDim (f.fiber y) = d)
      (F : X.Modules) [F.IsCoherent] (p : ℕ) (hp : d < (p : WithBot ℕ∞)),
      IsZero (AlgebraicGeometry.RingedSpace.stalkModuleCat
        (AlgebraicGeometry.RingedSpace.Hom.higherDirectImageModule f.toShHom F p) y))
