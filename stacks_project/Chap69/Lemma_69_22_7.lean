/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.FormalFunctions.Stalk
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.FormalFunctions
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory CategoryTheory.Limits

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `cohomologyOver`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- Lemma 69.22.7: let `S` be a scheme, let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`, and let `F` be a quasi-coherent sheaf on `X`. Assume `Y` locally
Noetherian, `f` proper, and `F` coherent. Let `ȳ` be a geometric point of `Y`.
Writing `X_n = space f ȳ n` for the infinitesimal neighbourhood
`Spec(O_{Y,ȳ}/m_ȳ^n) ×_Y X`, with `i_n = toX f ȳ n`, `f_n = toSpec f ȳ n`,
`c_n = toY ȳ n`, and `F_n = sheaf f F ȳ n`, the comparison
`limitComparison f F ȳ p` from the `m_ȳ`-adic completion of
`(R^p f_* F)_ȳ` to `lim_n H^p(X_n, F_n)` is an isomorphism of
`O_{Y,ȳ}^∧`-modules. -/
@[stacks 08B1] #check
  (AlgebraicGeometry.AlgebraicSpace.FormalFunctions.isIso_limitComparison :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsLocallyNoetherian Y] (f : X ⟶ Y) [Proper f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsCoherent] (ybar : GeometricPoint Y)
    [Abelian X.Modules] [Abelian Y.Modules]
    [∀ n, Abelian (space f ybar n).Modules]
    [∀ n, Abelian (thickening ybar n).Modules]
    [Abelian (spaceInf f ybar).Modules]
    [Abelian (specSpace ybar).Modules]
    [HasInjectiveResolutions X.Modules]
    [∀ n, HasInjectiveResolutions (space f ybar n).Modules]
    [HasInjectiveResolutions (spaceInf f ybar).Modules] (p : ℕ),
    IsIso (limitComparison f F ybar p))
