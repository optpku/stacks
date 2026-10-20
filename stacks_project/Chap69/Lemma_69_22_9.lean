/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HigherDirectImage.CoherentVanishing
import StacksCheckRecall

/-!
# Vanishing of geometric stalks of higher direct images above fibre dimension

For a proper morphism of algebraic spaces with locally Noetherian target, the geometric
stalk of `R^p f_* F` at `ȳ` vanishes in degrees strictly larger than `dim(X_ȳ)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.FormalFunctions
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- Lemma 69.22.9: let `S` be a scheme, let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`, and let `ȳ` be a geometric point of `Y`. Assume `Y` locally
Noetherian, `f` proper, and `dim(X_ȳ) = d`, where the geometric fibre is
`X_ȳ = fiber f ȳ = space f ȳ 1 = Spec(κ(ȳ)) ×_Y X`. Then for every coherent
`𝒪_X`-module `F` and every `p > d`, the geometric stalk `(R^p f_* F)_ȳ` is zero. -/
@[stacks 0A4T] #check
  (AlgebraicGeometry.AlgebraicSpace.FormalFunctions.stalkModuleCat_isZero_of_proper_of_fiberDimension_eq :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Proper f] [IsLocallyNoetherian Y]
    [Abelian X.Modules] [Abelian Y.Modules] [HasInjectiveResolutions X.Modules]
    (ybar : GeometricPoint Y) (d : ℕ)
    (hdim : dimension (fiber f ybar) = (d : WithBot ℕ∞))
    (F : X.Modules) [F.IsCoherent] {p : ℕ} (hp : d < p),
    IsZero (stalkModuleCat ybar (Modules.higherDirectImage f F p)))

/- If `f` is proper, `Y` is locally Noetherian, and `dim(X_ȳ) < p`, then the geometric
stalk of `R^p f_* F` at `ȳ` vanishes for every coherent `𝒪_X`-module `F`. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.FormalFunctions.stalkModuleCat_isZero_of_lt_fiberDimension :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Proper f] [IsLocallyNoetherian Y]
    [Abelian X.Modules] [Abelian Y.Modules] [HasInjectiveResolutions X.Modules]
    (ybar : GeometricPoint Y) (F : X.Modules) [F.IsCoherent]
    {p : ℕ} (hp : dimension (fiber f ybar) < p),
    IsZero (stalkModuleCat ybar (Modules.higherDirectImage f F p)))
