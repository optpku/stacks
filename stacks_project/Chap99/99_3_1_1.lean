/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap99.«99_3_1_1_Functor»

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- 99.3.1.1: the Hom functor `Hom(F, G) : (Sch/B)ᵒᵖ ⥤ Sets` sending a scheme `T` over `B`
to the type of `𝒪_{X_T}`-module morphisms `F_T ⟶ G_T`, where `X_T = X ×_B T` and
`F_T`, `G_T` are the pullbacks along `X_T ⟶ X`. -/
@[stacks 08JU]
abbrev homFunctor {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] :=
  HomFunctor.functor f F G

/-- Evaluating the Hom functor at a scheme over `B` yields Hom of the base-changed modules. -/
theorem homFunctor_obj {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (σ : SchemeOver B) :
    (homFunctor f F G).obj (op σ) =
      (baseChangeModule f σ.hom F ⟶ baseChangeModule f σ.hom G) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
