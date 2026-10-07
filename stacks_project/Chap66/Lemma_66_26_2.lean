module

public import stacks_project.Chap67.«67_11_1_1_Comparison»
public import stacks_project.Chap69.«69_3_0_1_Comparison»
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

/- Lemma 66.26.2 (1): for a cartesian square of algebraic spaces over a scheme `S` with étale
bottom edge `g : Y' ⟶ Y`, restriction of `F ∈ Mod(𝒪_X)` along the étale edges commutes with
module pushforward: `f'_*(F|_{X'}) = (f_* F)|_{Y'}` in `Mod(𝒪_{Y'})`. -/
@[stacks 03LX] #check
  (Modules.pushforwardEtaleBaseChangeIso :
    ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
      {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y},
      IsPullback h f' f g → ∀ [Etale g] [Etale h] (F : X.Modules),
        (Modules.restrictFunctor g).obj ((Modules.pushforward f).obj F) ≅
          (Modules.pushforward f').obj (Modules.restrict F h))

/- Lemma 66.26.2 (2): in the situation of (1), restriction also commutes with higher direct
images: `R^i f'_*(F|_{X'}) = (R^i f_* F)|_{Y'}` in `Mod(𝒪_{Y'})`, as the existing identification
`(restrictFunctor g).obj (higherDirectImage f F i) ≅ higherDirectImage f' (restrict F h) i`. -/
@[stacks 03LX] #check Modules.higherDirectImageEtaleBaseChangeIso
