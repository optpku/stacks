module

public import stacks_project.Chap99.«99_7_1_2_Functor»

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

/-- 99.7.1.2: the functor of finitely presented quotients `Q^{fp}_{F/X/B}` of a
quasi-coherent `𝒪_X`-module `F` along a morphism `f : X ⟶ B` of algebraic
spaces over a scheme `S`. It is the subfunctor of `Q_{F/X/B}` sending a scheme
`T` over `B` to the set of kernel-identified quotients `F_T ⟶ Q` on
`X_T = X ×_B T` with `Q` quasi-coherent, flat over `T`, and of finite
presentation as an `𝒪_{X_T}`-module. Pullback of modules preserves finite
presentation, so this is a functor `(Sch/B)ᵒᵖ ⥤ Sets`. -/
@[stacks 0CZL]
abbrev quotFpFunctor {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    (F : X.Modules) [F.IsQuasicoherent] :=
  fpFunctor f F

/-- Evaluating the finitely presented quotient functor at a scheme over `B`
yields kernel-identified finitely presented quotient points of `F_T`. -/
theorem quotFpFunctor_obj {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    (F : X.Modules) [F.IsQuasicoherent] (σ : SchemesOver B) :
    (quotFpFunctor f F).obj (op σ) = _root_.Quotient (fpSetoid f F σ) := sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
