/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.IntegralPushforward
import StacksCheckRecall

/-!
# Exactness of small étale abelian pushforward along integral morphisms

For an integral morphism of algebraic spaces, the small étale abelian
direct image is exact, and the higher direct images vanish in positive degree.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Lemma 69.4.1 (1): let `S` be a scheme. Let `f : X ⟶ Y` be an integral morphism of
algebraic spaces over `S` (for example a finite morphism). Then
`sheafPushforwardAbelian f : Sheaf (smallEtaleTopology X) AddCommGrpCat ⥤
Sheaf (smallEtaleTopology Y) AddCommGrpCat` is an exact functor. -/
@[stacks 0A4K] #check
  (AlgebraicGeometry.AlgebraicSpace.sheafPushforwardAbelian_exact_of_isIntegralHom :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIntegralHom f],
      exactFunctor (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
        (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) (sheafPushforwardAbelian f))

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.rightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- Lemma 69.4.1 (2): let `S` be a scheme. Let `f : X ⟶ Y` be an integral morphism of
algebraic spaces over `S` (for example a finite morphism), and let `F` be an abelian
sheaf on the small étale site of `X`. Then `higherDirectImage f F p` is zero for
`0 < p`. -/
@[stacks 0A4K] #check
  (AlgebraicGeometry.AlgebraicSpace.higherDirectImage_isZero_of_isIntegralHom :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIntegralHom f]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [(sheafPushforward AddCommGrpCat.{u + 1} f).Additive]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) (p : ℕ) (hp : 0 < p),
      IsZero (higherDirectImage f F p))
