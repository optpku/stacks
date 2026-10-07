module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap66.Definition_66_12_5_Reduced
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact

/-!
# Nested open filtrations of algebraic spaces by scheme strata

This file owns nested open subspaces of an algebraic space together with
separated-scheme surjective étale presentations that are isomorphisms over
the successive reduced differences.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The point-set of the reduced difference `T_{n+1} = U_{n+1} \ U_{n+2}` associated
to a sequence of open subspaces, as a subset of `Points X`. -/
def stratumPoints (U : ℕ → OpenSubspace X) (n : ℕ) : Set (Points X) :=
  (U n).pointsSet \ (U (n + 1)).pointsSet

/-- Membership in `stratumPoints U n` means the point lies in the `n`-th open stage
and not in the next one. -/
theorem mem_stratumPoints (U : ℕ → OpenSubspace X) (n : ℕ) {x : Points X} :
    x ∈ stratumPoints U n ↔ x ∈ (U n).pointsSet ∧ x ∉ (U (n + 1)).pointsSet :=
  sorry

/-- The inverse image of `stratumPoints U n` in `|U n|` is closed, so it carries a
reduced induced closed subspace structure. -/
theorem isClosed_preimage_stratumPoints (U : ℕ → OpenSubspace X) (n : ℕ) :
    IsClosed ((Points.map (U n).ι) ⁻¹' stratumPoints U n) :=
  sorry

/-- The reduced induced closed subspace `T_{n+1} ⊂ U_{n+1}` on the inverse image of
the successive difference of open stages. -/
def reducedStratum (U : ℕ → OpenSubspace X) (n : ℕ) : ClosedSubspace (U n).X :=
  (ClosedSubspaceStructure.reduced
      ⟨(Points.map (U n).ι) ⁻¹' stratumPoints U n, isClosed_preimage_stratumPoints U n⟩).subspace

/-- The underlying point-set of `reducedStratum U n` is the inverse image of
`stratumPoints U n` in `|U n|`. -/
theorem reducedStratum_pointsSet (U : ℕ → OpenSubspace X) (n : ℕ) :
    (reducedStratum U n).pointsSet = (Points.map (U n).ι) ⁻¹' stratumPoints U n :=
  sorry

/-- The closed subspace `reducedStratum U n` is reduced in the étale-local sense. -/
theorem reducedStratum_isReduced (U : ℕ → OpenSubspace X) (n : ℕ) :
    hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u})
      (reducedStratum U n).X :=
  sorry

/-- A nested sequence of open subspaces of `X` equipped with separated-scheme
surjective étale presentations that are isomorphisms over the successive reduced
differences, covering every quasi-compact field-valued point of `X`. -/
structure SchemeStratumFiltration (X : AlgebraicSpace S) where
  /-- The nested open subspaces, with `openStage 0` corresponding to source `U_1 = X`. -/
  openStage : ℕ → OpenSubspace X
  /-- The presenting scheme `V_{n+1}` of the `n`-th open stage, as a scheme over `S`. -/
  schemeStage : ℕ → Over S
  /-- The presentation morphism `f_{n+1} : V_{n+1} ⟶ U_{n+1}`. -/
  cover (n : ℕ) : ofOver (schemeStage n) ⟶ (openStage n).X
  /-- The open stages are nested: `… ⊂ U₄ ⊂ U₃ ⊂ U₂ ⊂ U₁`. -/
  antitone_pointsSet : Antitone (fun n ↦ (openStage n).pointsSet)
  /-- The first open stage occupies all of `|X|`, encoding `U_1 = X`. -/
  pointsSet_zero : (openStage 0).pointsSet = Set.univ
  /-- Each presenting scheme `V_{n+1}` is separated. -/
  isSeparated_schemeStage (n : ℕ) : Scheme.IsSeparated (schemeStage n).left
  /-- Each presentation `f_{n+1}` is étale. -/
  etale_cover (n : ℕ) : Etale (cover n)
  /-- Each presentation `f_{n+1}` is surjective. -/
  surjective_cover (n : ℕ) : Surjective (cover n)
  /-- The restriction `f_{n+1}⁻¹(T_{n+1}) ⟶ T_{n+1}` is an isomorphism. -/
  isIso_cover_stratum (n : ℕ) :
    IsIso (pullback.snd (cover n) (reducedStratum openStage n).ι)
  /-- Every point of `|X|` represented by a quasi-compact morphism `Spec(k) ⟶ X`
  from a field lies in some reduced difference `T_p`. -/
  quasiCompactFieldPoint_mem_stratum (p : FieldValuedPoint X) (hp : QuasiCompact p.hom) :
    ∃ n, Points.mk p ∈ stratumPoints openStage n

namespace SchemeStratumFiltration

/-- Construct a scheme-stratum filtration from explicit open stages, presenting
schemes, cover morphisms, and the nested, separated, étale, surjective,
isomorphism-over-stratum, and quasi-compact field-point laws. -/
def ofStages (openStage : ℕ → OpenSubspace X) (schemeStage : ℕ → Over S)
    (cover : ∀ n, ofOver (schemeStage n) ⟶ (openStage n).X)
    (antitone_pointsSet : Antitone (fun n ↦ (openStage n).pointsSet))
    (pointsSet_zero : (openStage 0).pointsSet = Set.univ)
    (isSeparated_schemeStage : ∀ n, Scheme.IsSeparated (schemeStage n).left)
    (etale_cover : ∀ n, Etale (cover n)) (surjective_cover : ∀ n, Surjective (cover n))
    (isIso_cover_stratum :
      ∀ n, IsIso (pullback.snd (cover n) (reducedStratum openStage n).ι))
    (quasiCompactFieldPoint_mem_stratum :
      ∀ p : FieldValuedPoint X, QuasiCompact p.hom →
        ∃ n, Points.mk p ∈ stratumPoints openStage n) :
    SchemeStratumFiltration X where
  openStage := openStage
  schemeStage := schemeStage
  cover := cover
  antitone_pointsSet := antitone_pointsSet
  pointsSet_zero := pointsSet_zero
  isSeparated_schemeStage := isSeparated_schemeStage
  etale_cover := etale_cover
  surjective_cover := surjective_cover
  isIso_cover_stratum := isIso_cover_stratum
  quasiCompactFieldPoint_mem_stratum := quasiCompactFieldPoint_mem_stratum

/-- The open stages of a filtration built by `ofStages` are the supplied stages. -/
@[simp]
theorem ofStages_openStage (openStage : ℕ → OpenSubspace X) (schemeStage : ℕ → Over S)
    (cover : ∀ n, ofOver (schemeStage n) ⟶ (openStage n).X)
    (antitone_pointsSet : Antitone (fun n ↦ (openStage n).pointsSet))
    (pointsSet_zero : (openStage 0).pointsSet = Set.univ)
    (isSeparated_schemeStage : ∀ n, Scheme.IsSeparated (schemeStage n).left)
    (etale_cover : ∀ n, Etale (cover n)) (surjective_cover : ∀ n, Surjective (cover n))
    (isIso_cover_stratum :
      ∀ n, IsIso (pullback.snd (cover n) (reducedStratum openStage n).ι))
    (quasiCompactFieldPoint_mem_stratum :
      ∀ p : FieldValuedPoint X, QuasiCompact p.hom →
        ∃ n, Points.mk p ∈ stratumPoints openStage n) :
    (ofStages openStage schemeStage cover antitone_pointsSet pointsSet_zero
        isSeparated_schemeStage etale_cover surjective_cover isIso_cover_stratum
        quasiCompactFieldPoint_mem_stratum).openStage =
      openStage :=
  sorry

/-- The presenting schemes of a filtration built by `ofStages` are the supplied schemes. -/
@[simp]
theorem ofStages_schemeStage (openStage : ℕ → OpenSubspace X) (schemeStage : ℕ → Over S)
    (cover : ∀ n, ofOver (schemeStage n) ⟶ (openStage n).X)
    (antitone_pointsSet : Antitone (fun n ↦ (openStage n).pointsSet))
    (pointsSet_zero : (openStage 0).pointsSet = Set.univ)
    (isSeparated_schemeStage : ∀ n, Scheme.IsSeparated (schemeStage n).left)
    (etale_cover : ∀ n, Etale (cover n)) (surjective_cover : ∀ n, Surjective (cover n))
    (isIso_cover_stratum :
      ∀ n, IsIso (pullback.snd (cover n) (reducedStratum openStage n).ι))
    (quasiCompactFieldPoint_mem_stratum :
      ∀ p : FieldValuedPoint X, QuasiCompact p.hom →
        ∃ n, Points.mk p ∈ stratumPoints openStage n) :
    (ofStages openStage schemeStage cover antitone_pointsSet pointsSet_zero
        isSeparated_schemeStage etale_cover surjective_cover isIso_cover_stratum
        quasiCompactFieldPoint_mem_stratum).schemeStage =
      schemeStage :=
  sorry

/-- The cover morphisms of a filtration built by `ofStages` are the supplied covers. -/
@[simp]
theorem ofStages_cover (openStage : ℕ → OpenSubspace X) (schemeStage : ℕ → Over S)
    (cover : ∀ n, ofOver (schemeStage n) ⟶ (openStage n).X)
    (antitone_pointsSet : Antitone (fun n ↦ (openStage n).pointsSet))
    (pointsSet_zero : (openStage 0).pointsSet = Set.univ)
    (isSeparated_schemeStage : ∀ n, Scheme.IsSeparated (schemeStage n).left)
    (etale_cover : ∀ n, Etale (cover n)) (surjective_cover : ∀ n, Surjective (cover n))
    (isIso_cover_stratum :
      ∀ n, IsIso (pullback.snd (cover n) (reducedStratum openStage n).ι))
    (quasiCompactFieldPoint_mem_stratum :
      ∀ p : FieldValuedPoint X, QuasiCompact p.hom →
        ∃ n, Points.mk p ∈ stratumPoints openStage n) :
    (ofStages openStage schemeStage cover antitone_pointsSet pointsSet_zero
        isSeparated_schemeStage etale_cover surjective_cover isIso_cover_stratum
        quasiCompactFieldPoint_mem_stratum).cover =
      cover :=
  sorry

/-- The nested, endpoint, separated, étale, surjective, isomorphism-over-stratum,
and quasi-compact field-point conditions of a scheme-stratum filtration. -/
theorem spec (F : SchemeStratumFiltration X) :
    Antitone (fun n ↦ (F.openStage n).pointsSet) ∧
      (F.openStage 0).pointsSet = Set.univ ∧
      (∀ n, Scheme.IsSeparated (F.schemeStage n).left) ∧
      (∀ n, Etale (F.cover n)) ∧ (∀ n, Surjective (F.cover n)) ∧
      (∀ n, IsIso (pullback.snd (F.cover n) (reducedStratum F.openStage n).ι)) ∧
      ∀ p : FieldValuedPoint X, QuasiCompact p.hom →
        ∃ n, Points.mk p ∈ stratumPoints F.openStage n :=
  sorry

/-- In any pullback square for `cover n` along `reducedStratum n`, the projection
to the reduced stratum is an isomorphism. -/
theorem isIso_snd_of_isPullback (F : SchemeStratumFiltration X) (n : ℕ)
    {P : AlgebraicSpace S} {pV : P ⟶ ofOver (F.schemeStage n)}
    {pT : P ⟶ (reducedStratum F.openStage n).X}
    (h : IsPullback pV pT (F.cover n) (reducedStratum F.openStage n).ι) :
    IsIso pT :=
  sorry

end SchemeStratumFiltration

/-- A quasi-compact algebraic space admits a nested open filtration by scheme
strata with separated-scheme surjective étale presentations isomorphic over the
reduced differences, covering every quasi-compact field-valued point. -/
theorem exists_schemeStratumFiltration (X : AlgebraicSpace S) [IsQuasiCompact X] :
    Nonempty (SchemeStratumFiltration X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
