module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IsomSheaf

/-!
# Lemma 99.4.2

In Situation 99.3.1, morphisms of fppf sheaves from an algebraic space `T`
over `S` into `Isom(F, G)` are identified with pairs `(h, u)` where
`h : T ⟶ B` and `u : F_T ⟶ G_T` is an `𝒪_{X_T}`-module isomorphism.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 99.4.2: in Situation 99.3.1, let `T` be an algebraic space over `S`.
Morphisms of fppf sheaves `T ⟶ Isom(F, G)` on `(Sch/S)_fppf` are in bijection
with pairs `(h, u)` where `h : T ⟶ B` and `u : F_T ⟶ G_T` is an
`𝒪_{X_T}`-module isomorphism, with `X_T = X ×_{B,h} T` the pullback of `f`
along `h` and `F_T`, `G_T` the pullbacks of `F`, `G` along `X_T ⟶ X`. -/
@[stacks 0D3T] #check (AlgebraicGeometry.AlgebraicSpace.Modules.sheafIsom_bijective :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) (F G : X.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] (T : AlgebraicSpace S),
    Function.Bijective (AlgebraicGeometry.AlgebraicSpace.Modules.toSheafIsom f F G T))
