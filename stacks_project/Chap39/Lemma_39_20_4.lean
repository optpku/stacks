/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.LocalSurjectivity
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

/- Lemma 39.20.4 (1): two points have the same class in the quotient sheaf exactly when a
covering family makes them the source and target of local arrows in the pre-equivalence
relation. -/
@[stacks 045Y] #check
  (AlgebraicGeometry.Scheme.PreRelation.quotientClass_eq_iff_exists_cover :
    ∀ {S : Scheme.{u}} (τ : StandardTopology) {U : Over S}
      (P : Scheme.PreRelation U) (hP : P.IsPreEquivalence)
      (T : Over S) (a b : T ⟶ U),
        P.quotientClass (τ.overTopology S) a = P.quotientClass (τ.overTopology S) b ↔
          ∃ 𝒳 : SemiRepresentableFamily.Over.{u + 1} T,
            SemiRepresentableFamily.Over.IsCovering
              (τ.overTopology S).toPrecoverage 𝒳 ∧
              ∀ i : 𝒳.index, ∃ r : (𝒳.obj i).left ⟶ P.left,
                (𝒳.obj i).hom ≫ a = r ≫ P.s ∧
                  (𝒳.obj i).hom ≫ b = r ≫ P.t)

/- Lemma 39.20.4 (2): the represented relation maps locally surjectively onto the kernel pair
of the quotient map. -/
@[stacks 045Y] #check
  (AlgebraicGeometry.Scheme.PreRelation.relationToKernelPair_locallySurjective :
    ∀ {S : Scheme.{u}} (τ : StandardTopology) {U : Over S}
      (P : Scheme.PreRelation U) (hP : P.IsPreEquivalence),
        Sheaf.IsLocallySurjective (P.relationToKernelPair (τ.overTopology S)))
