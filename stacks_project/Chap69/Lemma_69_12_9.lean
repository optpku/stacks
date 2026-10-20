module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Finite
import StacksCheckRecall

/-!
# Lemma 69.12.9

Positive higher direct images of a coherent module along a finite morphism of
algebraic spaces vanish, and the underived pushforward remains coherent.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

section HigherDirectImage

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- Lemma 69.12.9
For a finite morphism of algebraic spaces with locally Noetherian target,
positive higher direct images of a coherent module vanish and its ordinary
pushforward is coherent.
-/
@[stacks 07UH] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.higherDirectImage_isZero_of_isFinite :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsFinite f]
    [IsLocallyNoetherian Y] [Abelian X.Modules] [Abelian Y.Modules]
    [HasInjectiveResolutions X.Modules] (F : X.Modules) [F.IsCoherent]
    (p : ℕ), 0 < p → IsZero (higherDirectImage f F p))

end HigherDirectImage

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.pushforward_obj_isCoherent_of_isFinite :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsFinite f]
    [IsLocallyNoetherian Y] (F : X.Modules) [F.IsCoherent],
    ((pushforward f).obj F).IsCoherent)

end AlgebraicGeometry.AlgebraicSpace.Modules
