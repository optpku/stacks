module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap69.«69_3_0_1_HigherDirectImage»
public import stacks_project.Chap69.Definition_69_12_1_Instances

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

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/-- Lemma 69.12.9 (1): if `f : X ⟶ Y` is a finite morphism of algebraic spaces over a scheme
`S` with `Y` locally Noetherian, and `F` is a coherent `𝒪_X`-module, then
`higherDirectImage f F p` is zero for `0 < p`. -/
@[stacks 07UH]
theorem higherDirectImage_isZero_of_isFinite
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsFinite f]
    [IsLocallyNoetherian Y] [Abelian X.Modules] [Abelian Y.Modules]
    [HasInjectiveResolutions X.Modules] (F : X.Modules) [F.IsCoherent]
    (p : ℕ) (hp : 0 < p) :
    IsZero (higherDirectImage f F p) :=
  sorry

/-- Lemma 69.12.9 (2): if `f : X ⟶ Y` is a finite morphism of algebraic spaces over a scheme
`S` with `Y` locally Noetherian, and `F` is a coherent `𝒪_X`-module, then
`(pushforward f).obj F` is coherent. -/
@[stacks 07UH]
instance pushforward_obj_isCoherent_of_isFinite
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsFinite f]
    [IsLocallyNoetherian Y] (F : X.Modules) [F.IsCoherent] :
    ((pushforward f).obj F).IsCoherent :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
