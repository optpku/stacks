module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology

/-!
# Vanishing of higher direct images above fibre dimension

For a proper morphism to a locally Noetherian scheme, the stalks of
higher direct images of a coherent module vanish at any point whose
scheme-theoretic fibre has dimension `d`, in all degrees `p > d`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- Lemma 30.20.9: let `f : X ⟶ Y` be a morphism of schemes and let `y` be a
point of `Y`. Assume `Y` is locally Noetherian, `f` is proper, and
`topologicalKrullDim (f.fiber y) = d`. Then for any coherent `𝒪_X`-module `F`
and every `p > d`, the stalk of `R^p f_* F` at `y` vanishes.

This is the coherent, locally Noetherian specialization of the later
quasicoherent vanishing theorem tagged `0E7D`; the finite-fibre case
`p > 0` is Lemma 30.20.8. -/
@[stacks 02V7]
theorem higherDirectImageModule_stalk_isZero_of_proper_fiberDimension
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsProper f]
    (y : Y) (d : ℕ) (hdim : topologicalKrullDim (f.fiber y) = (d : WithBot ℕ∞))
    (F : X.Modules) [F.IsCoherent] (p : ℕ) (hp : d < p) :
    IsZero (RingedSpace.stalkModuleCat
      (RingedSpace.Hom.higherDirectImageModule f.toShHom F p) y) := sorry

end AlgebraicGeometry.Scheme
