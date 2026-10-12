/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap99.Remark_99_7_2_BaseChange

/-!
# Remark 99.7.2

In Situation 99.7.1, a morphism `g : B' ⟶ B` of algebraic spaces over `S` identifies
the functors of quotients after base change to `X' = X ×_B B'`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B B' : AlgebraicSpace S}

/-- Remark 99.7.2 (1): in Situation 99.7.1, let `g : B' ⟶ B` be a morphism of algebraic
spaces over `S`. Set `X' = X ×_B B'` and write `F'` for the pullback of `F` to `X'`.
For a scheme `T` over `B'`, the values of the quotient functors satisfy
`Q_{F'/X'/B'}(T) ≃ Q_{F/X/B}(T)`, where on the right `T` is viewed as a scheme over
`B` via the composition `T ⟶ B' ⟶ B`. -/
@[stacks 08IT]
def functor_changeBase_equiv (f : X ⟶ B) (g : B' ⟶ B) (F : X.Modules)
    [F.IsQuasicoherent] (σ : SchemesOver B') :
    (functor (pullback.snd f g) ((Modules.pullback (pullback.fst f g)).obj F)).obj (op σ) ≃
      (functor f F).obj (op ((CostructuredArrow.map g).obj σ)) :=
  ((functorChangeBaseIso f g F).app (op σ)).toEquiv

/-- The base-change equivalence of `Q_{F'/X'/B'}` is the component of
`functorChangeBaseIso`. -/
theorem functor_changeBase_equiv_spec (f : X ⟶ B) (g : B' ⟶ B) (F : X.Modules)
    [F.IsQuasicoherent] (σ : SchemesOver B') :
    functor_changeBase_equiv f g F σ =
      ((functorChangeBaseIso f g F).app (op σ)).toEquiv :=
  sorry

/-- Remark 99.7.2 (2): the same base-change identification holds for the finitely
presented quotient functors `Q^{fp}_{F'/X'/B'}` and `Q^{fp}_{F/X/B}`. -/
@[stacks 08IT]
def fpFunctor_changeBase_equiv (f : X ⟶ B) (g : B' ⟶ B) (F : X.Modules)
    [F.IsQuasicoherent] (σ : SchemesOver B') :
    (fpFunctor (pullback.snd f g) ((Modules.pullback (pullback.fst f g)).obj F)).obj (op σ) ≃
      (fpFunctor f F).obj (op ((CostructuredArrow.map g).obj σ)) :=
  ((fpFunctorChangeBaseIso f g F).app (op σ)).toEquiv

/-- The base-change equivalence of `Q^{fp}_{F'/X'/B'}` is the component of
`fpFunctorChangeBaseIso`. -/
theorem fpFunctor_changeBase_equiv_spec (f : X ⟶ B) (g : B' ⟶ B) (F : X.Modules)
    [F.IsQuasicoherent] (σ : SchemesOver B') :
    fpFunctor_changeBase_equiv f g F σ =
      ((fpFunctorChangeBaseIso f g F).app (op σ)).toEquiv :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
