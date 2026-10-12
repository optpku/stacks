/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap99.«99_8_1_1_Functor»
public import stacks_project.Chap99.Proposition_99_8_4_Representable

/-!
# Proposition 99.8.4

If `f : X ⟶ B` is a finitely presented separated morphism of algebraic spaces
over a scheme `S` and `F` is a quasi-coherent sheaf on `X`, then the Quot
functor `Quot_{F/X/B}` is an algebraic space. If also `F` is of finite
presentation, then `Quot_{F/X/B} ⟶ B` is locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

/-- Proposition 99.8.4 (1): if `f : X ⟶ B` is a finitely presented separated
morphism of algebraic spaces over a scheme `S` and `F` is a quasi-coherent
sheaf on `X`, then `Quot_{F/X/B}` is an algebraic space. In the Situation
99.8.1 reading, the associated functor on `(Sch/S)ᵒᵖ` sending `T` to pairs
`(h : T ⟶ B, Q)` is an algebraic space over `S`, equivalently represented over
`B` by `yonedaOver π` for some morphism `π` of algebraic spaces over `B`. -/
@[stacks 09TU]
theorem quot_isAlgebraicSpaceOver {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) [FinitePresentation f] [Separated f] (F : X.Modules)
    [F.IsQuasicoherent] : IsAlgebraicSpaceOver (quot f F) :=
  sorry

/-- Proposition 99.8.4 (2): under the hypotheses of clause (1), if also `F` is
of finite presentation, then `Quot_{F/X/B} ⟶ B` is locally of finite
presentation. -/
@[stacks 09TU]
theorem quot_isLocallyOfFinitePresentationOver {S : Scheme.{u}}
    {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] :
    IsLocallyOfFinitePresentationOver (quot f F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
