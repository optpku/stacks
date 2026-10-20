module

public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.CoherentVanishing
import StacksCheckRecall

/-!
# Vanishing of higher direct images on finite fibres

For a proper morphism to a locally Noetherian scheme, the stalks of
positive higher direct images of a coherent module vanish at any point
with finite fibre.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 30.20.8: let `f : X ⟶ Y` be a morphism of schemes and let `y` be a
point of `Y`. Assume `Y` is locally Noetherian, `f` is proper, and the fibre
`f ⁻¹' {y}` is finite. Then for any coherent `𝒪_X`-module `F` and every
`p > 0`, the stalk of `R^p f_* F` at `y` vanishes. -/
@[stacks 02OE] #check
  (AlgebraicGeometry.Scheme.higherDirectImageModule_stalk_isZero_of_proper_finite_fiber :
    ∀ {X Y : Scheme.{u}} [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsProper f]
      (y : Y) (hy : Set.Finite (f ⁻¹' ({y} : Set Y)))
      (F : X.Modules) [F.IsCoherent] (p : ℕ) (hp : 0 < p),
      IsZero (RingedSpace.stalkModuleCat
        (RingedSpace.Hom.higherDirectImageModule f.toShHom F p) y))

end AlgebraicGeometry.Scheme
