/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap96.Lemma_96_19_10_LocallyOfFinitePresentation
public import stacks_project.Chap100.Lemma_100_11_1_Flat
public import stacks_project.Chap101.Definition_101_4_2_Separation

/-!
# Quasi-DM algebraic stacks via locally quasi-finite flat scheme covers

An algebraic stack is quasi-DM if and only if it admits a surjective, flat,
locally finitely presented, locally quasi-finite morphism from a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- There exists a scheme `W` over `S` and a surjective, flat, locally of
finite presentation, locally quasi-finite morphism
`GroupoidsOver.slice W ⟶ X`. -/
def existsLocallyQuasiFiniteFlatCover {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] : Prop :=
  ∃ (W : Over S) (f : GroupoidsOver.slice W ⟶ X),
    Groupoids.Hom.Surjective f ∧ Groupoids.Hom.Flat f ∧
      Groupoids.Hom.LocallyOfFinitePresentation f ∧
      Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S) f

namespace existsLocallyQuasiFiniteFlatCover

/-- `existsLocallyQuasiFiniteFlatCover X` unpacks to a surjective, flat,
locally of finite presentation, locally quasi-finite morphism from a scheme
over `S`. -/
theorem iff {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    existsLocallyQuasiFiniteFlatCover X ↔
      ∃ (W : Over S) (f : GroupoidsOver.slice W ⟶ X),
        Groupoids.Hom.Surjective f ∧ Groupoids.Hom.Flat f ∧
          Groupoids.Hom.LocallyOfFinitePresentation f ∧
          Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S) f :=
  sorry

/-- A surjective, flat, locally of finite presentation, locally quasi-finite
morphism from a scheme over `S` witnesses
`existsLocallyQuasiFiniteFlatCover`. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {W : Over S} (f : GroupoidsOver.slice W ⟶ X) [Groupoids.Hom.Surjective f]
    [Groupoids.Hom.Flat f] [Groupoids.Hom.LocallyOfFinitePresentation f]
    (h_locallyQuasiFinite :
      Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S) f) :
    existsLocallyQuasiFiniteFlatCover X :=
  sorry

/-- `existsLocallyQuasiFiniteFlatCover X` supplies a surjective, flat, locally
of finite presentation, locally quasi-finite morphism from a scheme over
`S`. -/
theorem spec {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (h : existsLocallyQuasiFiniteFlatCover X) :
    ∃ (W : Over S) (f : GroupoidsOver.slice W ⟶ X),
      Groupoids.Hom.Surjective f ∧ Groupoids.Hom.Flat f ∧
        Groupoids.Hom.LocallyOfFinitePresentation f ∧
        Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S) f :=
  sorry

end existsLocallyQuasiFiniteFlatCover

/-- Theorem 101.21.3: Let `X` be an algebraic stack. The following are
equivalent: `X` is quasi-DM, and there exists a scheme `W` and a surjective,
flat, locally finitely presented, locally quasi-finite morphism `W ⟶ X`. -/
@[stacks 06MF]
theorem isQuasiDM_iff_existsLocallyQuasiFiniteFlatCover {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] :
    IsQuasiDM X ↔ existsLocallyQuasiFiniteFlatCover X :=
  sorry

/-- A surjective, flat, locally of finite presentation, locally quasi-finite
morphism from a scheme implies that the target algebraic stack is quasi-DM. -/
theorem isQuasiDM_of_existsLocallyQuasiFiniteFlatCover {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X]
    (h : existsLocallyQuasiFiniteFlatCover X) : IsQuasiDM X :=
  sorry

/-- A quasi-DM algebraic stack admits a surjective, flat, locally of finite
presentation, locally quasi-finite morphism from a scheme. -/
theorem existsLocallyQuasiFiniteFlatCover_of_isQuasiDM {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] [IsQuasiDM X] :
    existsLocallyQuasiFiniteFlatCover X :=
  sorry

end AlgebraicGeometry.AlgebraicStack
