/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Nerve.Target
import StacksCheckRecall

/-!
# Lemma 85.29.3

A groupoid scheme over `S` determines a cartesian morphism `t_•` from the Čech nerve of `s`
to the associated simplicial scheme, with the stated low-degree identifications.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Simplicial

universe u

/- Lemma 85.29.3 (1): let `(U, R, s, t, c)` be a groupoid scheme over a scheme `S`, let `X` be
the simplicial scheme constructed in Lemma 85.29.1, and let `(R/U)_•` be the Čech nerve of
`s`. There is a cartesian morphism `t_• : (R/U)_• ⟶ X`. -/
@[stacks 07TQ]
#check (AlgebraicGeometry.GroupoidScheme.targetSimplicial :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S),
      Scheme.Hom.simplicialScheme G.s.left ⟶ AlgebraicGeometry.GroupoidScheme.simplicialScheme G)

/- Lemma 85.29.3 (2): `t_•` is a cartesian morphism of simplicial schemes. -/
@[stacks 07TQ]
#check (AlgebraicGeometry.GroupoidScheme.targetSimplicial_isPullback :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S)
      {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m),
      IsPullback ((AlgebraicGeometry.GroupoidScheme.targetSimplicial G).app n)
        ((Scheme.Hom.simplicialScheme G.s.left).map f)
        ((AlgebraicGeometry.GroupoidScheme.simplicialScheme G).map f)
        ((AlgebraicGeometry.GroupoidScheme.targetSimplicial G).app m))

/- Lemma 85.29.3 (3): after identifying degree `0` of `(R/U)_•` with `R` and degree `0` of `X`
with `U`, the component of `t_•` is the target map `t`. -/
@[stacks 07TQ]
#check (AlgebraicGeometry.GroupoidScheme.targetSimplicial_app_zero :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S),
      (Arrow.cechNerve.degreeZero.iso (Arrow.mk G.s.left)).inv ≫
          (AlgebraicGeometry.GroupoidScheme.targetSimplicial G).app (op ⦋0⦌) ≫
          (AlgebraicGeometry.GroupoidScheme.degreeZero.iso G).hom = G.t.left)

/- Lemma 85.29.3 (4): after identifying degree `1` of `(R/U)_•` with `R ×_{s,U,s} R` and degree
`1` of `X` with `R`, the component of `t_•` is right division `(r₀, r₁) ↦ r₀ ∘ r₁⁻¹`. -/
@[stacks 07TQ]
#check (AlgebraicGeometry.GroupoidScheme.targetSimplicial_app_one :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S),
      (Arrow.cechNerve.degreeOne.pullbackIso (Arrow.mk G.s.left)).inv ≫
          (AlgebraicGeometry.GroupoidScheme.targetSimplicial G).app (op ⦋1⦌) ≫
          (AlgebraicGeometry.GroupoidScheme.degreeOne.iso G).hom =
        (PreservesPullback.iso (Over.forget S) G.s G.s).inv ≫ G.rightDivision.left)

/- Lemma 85.29.3 (5): after identifying degree `2` of `X` with `R ×_{s,U,t} R`, the first factor
of `t_•` is `r₀ ∘ r₁⁻¹`. -/
@[stacks 07TQ]
#check (AlgebraicGeometry.GroupoidScheme.targetSimplicial_app_two_fst :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S),
      (AlgebraicGeometry.GroupoidScheme.targetSimplicial G).app (op ⦋2⦌) ≫
          (AlgebraicGeometry.GroupoidScheme.degreeTwo.iso G).hom ≫
          (pullback.fst G.s G.t).left =
        (AlgebraicGeometry.GroupoidScheme.sourceCechRightDivision G (op ⦋2⦌) 0).left)

/- Lemma 85.29.3 (6): after identifying degree `2` of `X` with `R ×_{s,U,t} R`, the second factor
of `t_•` is `r₁ ∘ r₂⁻¹`. -/
@[stacks 07TQ]
#check (AlgebraicGeometry.GroupoidScheme.targetSimplicial_app_two_snd :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S),
      (AlgebraicGeometry.GroupoidScheme.targetSimplicial G).app (op ⦋2⦌) ≫
          (AlgebraicGeometry.GroupoidScheme.degreeTwo.iso G).hom ≫
          (pullback.snd G.s G.t).left =
        (AlgebraicGeometry.GroupoidScheme.sourceCechRightDivision G (op ⦋2⦌) 1).left)
