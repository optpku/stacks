module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HigherDirectImage.CoherentVanishing
import StacksCheckRecall

/-!
# Lemma 69.22.8

Positive higher direct images of a coherent module along a proper morphism of
algebraic spaces have vanishing geometric stalks over a locally Noetherian
target, whenever the geometric fibre is discrete.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.FormalFunctions
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- Lemma 69.22.8: let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. Let `ȳ` be a geometric point of `Y`. Assume `Y` locally Noetherian,
`f` is proper, and the geometric fibre `fiber f ȳ` has discrete space of points.
Then for any coherent sheaf `F` on `X`, the geometric stalk
`stalkModuleCat ȳ (higherDirectImage f F p)` is zero for all `p > 0`. -/
@[stacks 0A4S] #check
  (AlgebraicGeometry.AlgebraicSpace.FormalFunctions.stalkModuleCat_higherDirectImage_isZero_of_discreteFiber :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [Proper f]
    (F : X.Modules) [F.IsCoherent] (ybar : GeometricPoint Y)
    [Abelian X.Modules] [Abelian Y.Modules]
    [HasInjectiveResolutions X.Modules]
    (h_discrete : DiscreteTopology (Points (fiber f ybar)))
    (p : ℕ) (hp : 0 < p),
    IsZero (stalkModuleCat ybar (Modules.higherDirectImage f F p)))
