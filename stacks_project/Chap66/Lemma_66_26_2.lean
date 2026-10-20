module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.EtaleBaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HigherDirectImage.EtaleBaseChange
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

/- Lemma 66.26.2 (1): for a cartesian square of algebraic spaces over a scheme `S` with étale
bottom edge `g : Y' ⟶ Y`, restriction of `F ∈ Mod(𝒪_X)` along the étale edges commutes with
module pushforward: `f'_*(F|_{X'}) = (f_* F)|_{Y'}` in `Mod(𝒪_{Y'})`.
The certificate `Etale h` follows from the cartesian square and `Etale g`. -/
@[stacks 03LX] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.pushforwardEtaleBaseChangeIso :
    ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
      {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y},
      IsPullback h f' f g → ∀ [Etale g] [Etale h] (F : X.Modules),
        (Modules.restrictFunctor g).obj ((Modules.pushforward f).obj F) ≅
          (Modules.pushforward f').obj (Modules.restrict F h))

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.RightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImageEtaleBaseChangeHom`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- Lemma 66.26.2 (2): in the situation of (1), restriction also commutes with higher direct
images: `R^i f'_*(F|_{X'}) = (R^i f_* F)|_{Y'}` in `Mod(𝒪_{Y'})`, as the existing identification
`(restrictFunctor g).obj (higherDirectImage f F i) ≅ higherDirectImage f' (restrict F h) i`.
As above, `Etale h` follows from the cartesian square and `Etale g`. The Abelian category and
injective-resolution instances are standard formal prerequisites for these derived functors. -/
@[stacks 03LX] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.higherDirectImageEtaleBaseChangeIso :
    ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
      {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
      (h_cart : IsPullback h f' f g) [Etale g] [Etale h]
      [Abelian X.Modules] [Abelian X'.Modules] [Abelian Y.Modules] [Abelian Y'.Modules]
      [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules]
      (F : X.Modules) (i : ℕ),
      (Modules.restrictFunctor g).obj (Modules.higherDirectImage f F i) ≅
        Modules.higherDirectImage f' (Modules.restrict F h) i)
