/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.Basic

/-!
# Valuative covering families

This module defines `V` coverings as families admitting standard valuative
refinements over every affine open of their target.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

/-- A family of maps to `T` is a `V` covering when every
affine open of `T` admits a standard `V` cover refining the pulled-back
family. -/
def IsVCovering {ι : Type v} (T : Scheme.{u}) (family : ι → Scheme.{u})
    (map : ∀ i, family i ⟶ T) : Prop :=
  ∀ U : T.affineOpens,
    ∃ refining : AffineFamilyOver U,
      AffineFamilyOver.IsStandardVCover refining ∧
        ∃ chart : Fin refining.n → ι,
          ∀ j,
            ∃ lift : refining.U j ⟶ pullback (map (chart j)) ((U : T.Opens).ι),
              lift ≫ pullback.snd (map (chart j)) ((U : T.Opens).ι) = refining.map j

/-- A `V` covering admits its standard valuative refinement over a chosen
affine open. -/
theorem IsVCovering.exists_affineOpen_refinement
    {ι : Type v} {T : Scheme.{u}} {family : ι → Scheme.{u}}
    {map : ∀ i, family i ⟶ T} (h : IsVCovering T family map)
    (U : T.affineOpens) :
    ∃ refining : AffineFamilyOver U,
      AffineFamilyOver.IsStandardVCover refining ∧
        ∃ chart : Fin refining.n → ι,
          ∀ j,
            ∃ lift : refining.U j ⟶ pullback (map (chart j)) ((U : T.Opens).ι),
              lift ≫ pullback.snd (map (chart j)) ((U : T.Opens).ι) = refining.map j := sorry

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

variable {T : Scheme.{u}} {ι : Type v}

/-- The `V`-covering predicate for an indexed family in the slice over `T`. -/
abbrev VCovering (family : ι → Over T) : Prop :=
  IsVCovering T (fun i ↦ (family i).left) (fun i ↦ (family i).hom)

/-- The slice-family formulation of `VCovering` unfolds to the corresponding
raw family of source schemes and structure morphisms. -/
theorem vCovering_iff (family : ι → Over T) :
    VCovering family ↔
      IsVCovering T (fun i ↦ (family i).left) (fun i ↦ (family i).hom) := sorry

end AlgebraicGeometry.Scheme
