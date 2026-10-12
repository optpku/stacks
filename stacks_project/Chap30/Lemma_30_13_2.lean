/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.Pushforward
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 30.13.2: for an affine morphism `f : Y ⟶ X`, a quasi-coherent module `ℱ` on `Y`,
and ideal-sheaf data `I` on `X`, multiplication of `f_*ℱ` by `I` equals the pushforward of
multiplication of `ℱ` by the pulled-back ideal. -/
@[stacks 01YP] #check
  (AlgebraicGeometry.Scheme.Modules.idealPowerProductSubobject_pushforward_eq_map_of_isAffineHom :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f]
      (ℱ : Y.Modules) [ℱ.IsQuasicoherent] (I : X.IdealSheafData),
      AlgebraicGeometry.Scheme.Modules.idealPowerProductSubobject
          I ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj ℱ) 1 =
        (Subobject.map
            ((AlgebraicGeometry.Scheme.Modules.pushforward f).map
              (AlgebraicGeometry.Scheme.Modules.idealPowerProductSubobject
                (I.comap f) ℱ 1).arrow)).obj ⊤)
