module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HomSheaf

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 99.3.3: in Situation 99.3.1, morphisms of fppf sheaves from an algebraic
space `T` over `S` to `Hom(F, G)` correspond to pairs `(h, u)`, where `h : T ⟶ B`
and `u : F_T ⟶ G_T` is a module morphism on `X ×_{B,h} T`. -/
@[stacks 0D3S] #check (AlgebraicGeometry.AlgebraicSpace.Modules.sheafHom_bijective :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) (F G : X.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] (T : AlgebraicSpace S),
    Function.Bijective (AlgebraicGeometry.AlgebraicSpace.Modules.toSheafHom f F G T))
