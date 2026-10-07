module

public import stacks_project.Chap99.Lemma_99_14_11_Strong_formal_effectiveness_for_polarized_schemes_System

/-!
# Strong formal effectiveness for polarized schemes

Algebraization of a cartesian tower of proper flat finite-presentation schemes
with compatible invertible modules, ample at the first stage, over the spectrum
of a sequential inverse limit of rings.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

/-- Lemma 99.14.11 (Strong formal effectiveness for polarized schemes).
Let `(R_n)` be a sequential inverse system of rings with surjective transition
maps whose kernels are locally nilpotent, and set `R = lim R_n`,
`S_n = Spec (R_n)`, and `S = Spec R`. Given a commutative diagram of schemes
`X n ⟶ S_n` with cartesian squares and invertible modules `L n` on `X n`
together with isomorphisms `(step n)^* L (n + 1) ≅ L n`, if each
`X n ⟶ S_n` is proper, flat, and of finite presentation and `L 0` is ample
on `X 0` (Lean stage `0` is source `n = 1`), then there exists a morphism
`X ⟶ S` which is proper, flat, and of finite presentation, an ample invertible
`O_X`-module `L`, and compatible identifications `X n ≅ X ×_S S_n` and
`L n ≅ (cX n)^* L`. The stored `IsPullback` data recover the fibre-product
isomorphisms via `IsPullback.isoPullback`. -/
@[stacks 0D4T]
theorem strongFormalEffectiveness (ξ : FormalSystem.{u}) :
    ∃ (X : Scheme.{u}) (f : X ⟶ ξ.limitSpec) (L : X.Modules)
      (hf_proper : IsProper f) (hf_flat : Flat f)
      (hf_fp : Scheme.Hom.FinitePresentation f)
      (hL_inv : Scheme.Modules.Invertible L)
      (hL_ample : @Scheme.Modules.IsAmple X L hL_inv)
      (cX : ∀ n, ξ.X n ⟶ X)
      (hcX_pullback : ∀ n, IsPullback (cX n) (ξ.hom n) f (ξ.stageToLimit n))
      (cL : ∀ n, (Scheme.Modules.pullback (cX n)).obj L ≅ ξ.line n)
      (hcX_comp : ∀ n, cX n = ξ.step n ≫ cX (n + 1)),
      ∀ n,
        cL n =
          (Scheme.Modules.pullbackCongr (hcX_comp n)).app L ≪≫
            (Scheme.Modules.pullbackComp (ξ.step n) (cX (n + 1))).symm.app L ≪≫
              (Scheme.Modules.pullback (ξ.step n)).mapIso (cL (n + 1)) ≪≫
                ξ.iso n :=
  sorry

end AlgebraicGeometry.Polarized
