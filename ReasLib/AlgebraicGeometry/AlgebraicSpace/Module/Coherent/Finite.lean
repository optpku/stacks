module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite

/-!
# Coherent modules along finite morphisms of algebraic spaces

Finite pushforward to a locally Noetherian algebraic space preserves coherence,
and positive higher direct images of coherent modules vanish.
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

/-- Positive higher direct images of a coherent module along a finite morphism
of algebraic spaces with locally Noetherian target vanish. -/
@[stacks 07UH]
theorem higherDirectImage_isZero_of_isFinite
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsFinite f]
    [IsLocallyNoetherian Y] [Abelian X.Modules] [Abelian Y.Modules]
    [HasInjectiveResolutions X.Modules] (F : X.Modules) [F.IsCoherent]
    (p : ℕ) (hp : 0 < p) :
    IsZero (higherDirectImage f F p) :=
  sorry

end HigherDirectImage

/-- Pushforward along a finite morphism of algebraic spaces with locally
Noetherian target carries coherent modules to coherent modules. -/
@[stacks 07UH]
instance pushforward_obj_isCoherent_of_isFinite
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsFinite f]
    [IsLocallyNoetherian Y] (F : X.Modules) [F.IsCoherent] :
    ((pushforward f).obj F).IsCoherent :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
