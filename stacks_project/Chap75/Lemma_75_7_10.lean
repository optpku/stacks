module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HigherDirectImage.Coherent

/-!
# Lemma 75.7.10

Every higher direct image of a coherent module with support proper over a
locally Noetherian algebraic space, along a locally of finite type morphism of
algebraic spaces, is coherent.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- Lemma 75.7.10: if `f : X ⟶ Y` is a locally of finite type morphism of
algebraic spaces over a scheme `S` with `Y` locally Noetherian, and `F` is a
coherent `𝒪_X`-module whose support is proper over `Y`, then
`higherDirectImage f F p` is a coherent `𝒪_Y`-module for every `p : ℕ`. -/
@[stacks 08GC] #check (AlgebraicGeometry.AlgebraicSpace.Modules.higherDirectImage_isCoherent_of_properSupport :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [IsLocallyNoetherian Y] [Abelian X.Modules] [Abelian Y.Modules]
    [HasInjectiveResolutions X.Modules] (F : X.Modules) [F.IsCoherent]
    (hF : ClosedSubset.ProperOver f (closedSupport F)) (p : ℕ),
    (higherDirectImage f F p).IsCoherent)

end AlgebraicGeometry.AlgebraicSpace.Modules
