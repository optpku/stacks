/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HigherDirectImage.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.AffineBaseChange
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 69.11.1: for every cartesian diagram 69.11.0.1 and every quasi-coherent module,
the canonical base-change comparison along an affine morphism is an isomorphism. -/
@[stacks 07U8] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.isIso_baseChange_of_affine :
    ∀ {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
      (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
      (h_cart : IsPullback g' f' f g) [Affine f] (F : X.Modules) [F.IsQuasicoherent],
      IsIso ((Modules.baseChange h_cart.w).app F))

section

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Affine f]
variable (F : X.Modules) [F.IsQuasicoherent]

/- Pushforward along an affine morphism preserves quasi-coherence. -/
#check
  (Modules.pushforward.isQuasicoherent f F :
    ((Modules.pushforward f).obj F).IsQuasicoherent)

end

section

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- Lemma 69.11.1 (2): along an affine morphism of algebraic spaces, `R^i f_* ℱ` vanishes for
`0 < i`; together with `rightDerivedZeroIsoSelf` this is `f_* ℱ ≅ Rf_* ℱ`. -/
@[stacks 07U8] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.higherDirectImage_isZero_of_affine :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Affine f]
      [Abelian X.Modules] [Abelian Y.Modules] [HasInjectiveResolutions X.Modules]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent] (i : ℕ),
      0 < i → IsZero (Modules.higherDirectImage f ℱ i))

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Affine f]
variable [Abelian X.Modules] [Abelian Y.Modules] [HasInjectiveResolutions X.Modules]

#check
  ((Modules.pushforward f).rightDerivedZeroIsoSelf :
    (Modules.pushforward f).rightDerived 0 ≅ Modules.pushforward f)

end

/- Lemma 69.11.1 (3): for every cartesian diagram 69.11.0.1, `g^* f_* ℱ` is isomorphic to
`f'_* (g')^* ℱ`. -/
@[stacks 07U8] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.affineBaseChange_pushforward_isomorphic :
    ∀ {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
      (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y),
      IsPullback g' f' f g → ∀ [Affine f] (ℱ : X.Modules) [ℱ.IsQuasicoherent],
        IsIsomorphic ((Modules.pullback g).obj ((Modules.pushforward f).obj ℱ))
          ((Modules.pushforward f').obj ((Modules.pullback g').obj ℱ)))
