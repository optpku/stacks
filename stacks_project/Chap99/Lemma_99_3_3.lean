module

public import stacks_project.Chap99.Lemma_99_3_3_SpaceHom
public import stacks_project.Chap99.Lemma_99_3_3_Sheaf

/-!
# Lemma 99.3.3

In Situation 99.3.1, morphisms of fppf sheaves from an algebraic space `T`
over `S` into `Hom(F, G)` are identified with pairs `(h, u)` where
`h : T ⟶ B` and `u : F_T ⟶ G_T` is an `𝒪_{X_T}`-module map.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 99.3.3: in Situation 99.3.1, let `T` be an algebraic space over `S`.
Morphisms of fppf sheaves `T ⟶ Hom(F, G)` on `(Sch/S)_fppf` are in bijection
with pairs `(h, u)` where `h : T ⟶ B` and `u : F_T ⟶ G_T` is an
`𝒪_{X_T}`-module map, with `X_T = X ×_{B,h} T` the pullback of `f` along `h`
and `F_T`, `G_T` the pullbacks of `F`, `G` along `X_T ⟶ X`. -/
@[stacks 0D3S]
theorem sheafHom_bijective (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] (T : AlgebraicSpace S) :
    Function.Bijective (toSheafHom f F G T) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
