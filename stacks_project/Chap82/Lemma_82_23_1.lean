/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap71.Definition_71_6_1_EffectiveCartier
public import stacks_project.Chap71.Definition_71_7_1_AssociatedSheaf
public import stacks_project.Chap82.Definition_82_17_1_Cycle
public import stacks_project.Chap82.Definition_82_18_1_ChernCap
public import stacks_project.Chap82.Definition_82_22_1_Gysin
public import stacks_project.Chap82.Lemma_82_6_3_AssociatedCycle

/-!
# Gysin of a meromorphic divisor versus first Chern class on a Cartier divisor

On a good integral algebraic space, Gysin pullback of `div_N(t)` along an
effective Cartier divisor equals first-Chern cap of `N` restricted to the
zero scheme of the canonical section.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- Pullback of an invertible module along the zero-scheme immersion of
`𝒪_X(D)` remains invertible. -/
instance instIsInvertibleObject_pullback_zeroSchemeι
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    (D : ClosedSubspace X) [IsEffectiveCartierDivisor D.ι]
    (N : X.Modules) [isInvertibleObject N] :
    isInvertibleObject
      ((Modules.pullback
          (zeroSchemeι D.associatedSheaf D.canonicalSection)).obj N) :=
  Modules.isInvertibleObject_pullback
    (zeroSchemeι D.associatedSheaf D.canonicalSection) N

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable [IsIntegral X]

/-- The meromorphic-section divisor cycle `div_N(t)` is a `(k + 1)`-cycle when
`dim_δ(X) = (k + 1) + 1`. -/
theorem meromorphicSectionDivisorCycle_mem_succ
    (k : ℤ) (hX : deltaDimension f δ (univIrreducibleClosed X) = (k + 1) + 1)
    {N : X.Modules} [isInvertibleObject N]
    (t : meromorphicSections X N) (ht : IsRegularMeromorphicSection X N t) :
    meromorphicSectionDivisorCycle f δ t ht ∈ cycleGroup f δ (k + 1) :=
  sorry

/-- The associated `(k + 1)`-cycle of `Z(1_D)` as a space is a `(k + 1)`-cycle
on `Z(1_D)`. -/
theorem associatedCycle_id_zeroScheme_mem
    (k : ℤ) (D : ClosedSubspace X) [IsEffectiveCartierDivisor D.ι] :
    @ClosedSubspace.cycle S
        (zeroScheme D.associatedSheaf D.canonicalSection).X
        (LocallyOfFiniteType.isLocallyNoetherian
          (zeroSchemeι D.associatedSheaf D.canonicalSection ≫ f))
        (ClosedSubspace.id (zeroScheme D.associatedSheaf D.canonicalSection).X)
        (relativeDimensionFunction
          (zeroSchemeι D.associatedSheaf D.canonicalSection ≫ f) δ)
        (k + 1) ∈
      cycleGroup (zeroSchemeι D.associatedSheaf D.canonicalSection ≫ f) δ
        (k + 1) :=
  sorry

/-- Lemma 82.23.1: In Situation 82.2.1 let `X / B` be good. Assume `X` integral
and `n = dim_δ(X)`. Let `i : D ⟶ X` be an effective Cartier divisor. Let `N`
be an invertible `𝒪_X`-module and let `t` be a nonzero meromorphic section of
`N`. Then `i* div_N(t) = c1(N|_D) ∩ [D]_{n-1}` in `CH_{n-2}(D)`. Here
`n = (k + 1) + 1`, `i*` is Gysin of `(𝒪_X(D), 1_D)`, and `CH_k(D)` is the Chow
group of `Z(1_D)`. -/
@[stacks 0ER9]
theorem gysin_meromorphicSectionDivisorCycle_eq_firstChernClassCap
    (k : ℤ) (hX : deltaDimension f δ (univIrreducibleClosed X) = (k + 1) + 1)
    (D : ClosedSubspace X) [IsEffectiveCartierDivisor D.ι]
    (N : X.Modules) [isInvertibleObject N]
    (t : meromorphicSections X N) (ht : IsRegularMeromorphicSection X N t) :
    gysin f δ k D.associatedSheaf D.canonicalSection
        ⟨meromorphicSectionDivisorCycle f δ t ht,
          meromorphicSectionDivisorCycle_mem_succ f δ k hX t ht⟩ =
      firstChernClassCap
          (zeroSchemeι D.associatedSheaf D.canonicalSection ≫ f) δ
          ((Modules.pullback
              (zeroSchemeι D.associatedSheaf D.canonicalSection)).obj N) k
        ⟨@ClosedSubspace.cycle S
            (zeroScheme D.associatedSheaf D.canonicalSection).X
            (LocallyOfFiniteType.isLocallyNoetherian
              (zeroSchemeι D.associatedSheaf D.canonicalSection ≫ f))
            (ClosedSubspace.id
              (zeroScheme D.associatedSheaf D.canonicalSection).X)
            (relativeDimensionFunction
              (zeroSchemeι D.associatedSheaf D.canonicalSection ≫ f) δ)
            (k + 1),
          associatedCycle_id_zeroScheme_mem f δ k D⟩ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
