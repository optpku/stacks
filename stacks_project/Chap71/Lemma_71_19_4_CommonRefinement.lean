/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap71.Lemma_71_19_3_AdmissibleBlowup

/-!
# Common refinements of admissible blowups of algebraic spaces

A finite family of admissible blowups of a quasi-compact and quasi-separated
algebraic space has a common admissible refinement whose comparison morphisms
are themselves admissible blowups.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The inverse image of an open subspace `U` of `X` along `f : Y ⟶ X`, viewed
as an open subspace of `Y`, is the pullback of `U.ι` along `f`. -/
def OpenSubspace.inverseImage {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (U : OpenSubspace X) (f : Y ⟶ X) : OpenSubspace Y where
  X := pullback U.ι f
  ι := pullback.snd U.ι f
  isOpenImmersion := IsOpenImmersion.pullback_snd U.isOpenImmersion f

/-- The underlying space of `U.inverseImage f` is the fibre product of `U.ι`
and `f`. -/
theorem OpenSubspace.inverseImage_X {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (U : OpenSubspace X) (f : Y ⟶ X) :
    (U.inverseImage f).X = pullback U.ι f :=
  sorry

/-- The inclusion of `U.inverseImage f` into `Y` is the second projection of
the fibre product of `U.ι` and `f`. -/
theorem OpenSubspace.inverseImage_ι {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (U : OpenSubspace X) (f : Y ⟶ X) :
    (U.inverseImage f).ι = pullback.snd U.ι f :=
  sorry

/-- `U.inverseImage f` is the fibre product of `U.ι` and `f`, included into `Y`
by the second projection, and that inclusion is an open immersion. -/
theorem OpenSubspace.inverseImage_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (U : OpenSubspace X) (f : Y ⟶ X) :
    (U.inverseImage f).X = pullback U.ι f ∧
      (U.inverseImage f).ι = pullback.snd U.ι f ∧
        IsOpenImmersion (U.inverseImage f).ι :=
  sorry

/-- A finite family of blowups admissible over a quasi-compact open subspace of
a quasi-compact quasi-separated algebraic space has a common admissible
refinement, and every comparison morphism is admissible over the corresponding
inverse-image open subspace. -/
theorem exists_isAdmissibleBlowup_common_refinement
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (U : OpenSubspace X) [QuasiCompact U.ι]
    {n : ℕ} (Xi : Fin n → AlgebraicSpace S)
    (bi : ∀ i : Fin n, Xi i ⟶ X)
    (hbi : ∀ i : Fin n, IsAdmissibleBlowup U (bi i)) :
    ∃ (X' : AlgebraicSpace S) (b : X' ⟶ X),
      IsAdmissibleBlowup U b ∧
        ∀ i : Fin n, ∃ c : X' ⟶ Xi i,
          c ≫ bi i = b ∧ IsAdmissibleBlowup (U.inverseImage (bi i)) c :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
