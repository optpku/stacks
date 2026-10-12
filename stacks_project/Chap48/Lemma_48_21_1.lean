/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.NormalizedDualizing.Relative

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace.ModuleDerived

universe u

/- Lemma 48.21.1: let `S` be Noetherian, let `ωS` be a dualizing complex on `S`, and
let `X` be of finite type over `S` with dualizing complex `ωX` normalized relative to `ωS`.
If closed points `x : X` and `s : S` satisfy `X.obj.hom x = s`, and the derived stalk of
`ωS` at `s` is normalized dualizing over `𝒪_{S,s}`, then the derived stalk of `ωX` at `x`
is normalized dualizing over `𝒪_{X,x}`. -/
@[stacks 0AWL] #check
  (AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex.RelativeTo.stalk_isNormalizedDualizingComplex_of_closedPoint :
    ∀ {S : Scheme.{u}} [IsNoetherian S] (X : Scheme.FiniteTypeOver S)
    (x : X.obj.left) (s : S) (hx : x ∈ closedPoints X.obj.left)
    (hs : s ∈ closedPoints S) (hxs : X.obj.hom x = s)
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    (HS : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace))
    [MonoidalCategory (RingedSpace.ModuleDerived X.obj.left.toRingedSpace)]
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.obj.left.toRingedSpace))
    [MonoidalCategory (DerivedCategory (ModuleCat (S.presheaf.stalk s)))]
    (Hs : MonoidalClosed (DerivedCategory (ModuleCat (S.presheaf.stalk s))))
    [MonoidalCategory (DerivedCategory (ModuleCat (X.obj.left.presheaf.stalk x)))]
    (Hx : MonoidalClosed (DerivedCategory (ModuleCat (X.obj.left.presheaf.stalk x))))
    (ωS : RingedSpace.ModuleDerived S.toRingedSpace) (hωS : ωS.IsDualizingComplex HS)
    (ωX : RingedSpace.ModuleDerived X.obj.left.toRingedSpace)
    (hωX : @AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex.RelativeTo
      _ _ _ X.obj.hom (AlgebraicGeometry.Scheme.FiniteTypeOver.instFiniteType X)
      _ HS _ HX ωS hωS ωX)
    (hωS_s : (Stalk.obj ωS s).IsNormalizedDualizingComplex Hs),
    (Stalk.obj ωX x).IsNormalizedDualizingComplex Hx)
