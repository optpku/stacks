module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.CategoryTheory.Sites.Over.SheafCompose
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Relocalization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fppf.Comparison

/-! # Module sheafification on big algebraic-space sites -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale

variable {S : Scheme.{u}}

/-- Abelian-group-valued sheaf composition exists on `(Spaces/X)_étale`. -/
instance overEtaleTopology_hasSheafCompose (X : AlgebraicSpace S) :
    (overEtaleTopology X).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  sorry

/-- Abelian-group-valued weak sheafification exists on `(Spaces/X)_étale`. -/
instance overEtaleTopology_hasWeakSheafify (X : AlgebraicSpace S) :
    HasWeakSheafify (overEtaleTopology X) AddCommGrpCat.{u} :=
  sorry

/-- On `(Spaces/X)_étale`, sheafification equivalences are the locally bijective
morphisms. -/
instance overEtaleTopology_wEqualsLocallyBijective (X : AlgebraicSpace S) :
    (overEtaleTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  sorry

/-- Abelian-group-valued sheaf composition exists on every slice of
`(Spaces/X)_étale`. -/
instance overEtaleTopology_over_hasSheafCompose (X : AlgebraicSpace S) :
    ∀ U : Over X,
      ((overEtaleTopology X).over U).HasSheafCompose
        (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  fun U ↦ GrothendieckTopology.HasSheafCompose.over
    (overEtaleTopology X) (forget₂ RingCat.{u} AddCommGrpCat.{u}) U

/-- Abelian-group-valued weak sheafification exists on every slice of
`(Spaces/X)_étale`. -/
instance overEtaleTopology_over_hasWeakSheafify (X : AlgebraicSpace S) :
    ∀ U : Over X,
      HasWeakSheafify ((overEtaleTopology X).over U) AddCommGrpCat.{u} :=
  sorry

/-- On every slice of `(Spaces/X)_étale`, sheafification equivalences are the
locally bijective morphisms. -/
instance overEtaleTopology_over_wEqualsLocallyBijective (X : AlgebraicSpace S) :
    ∀ U : Over X,
      ((overEtaleTopology X).over U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Etale

namespace AlgebraicGeometry.AlgebraicSpace.Fppf

variable {S : Scheme.{u}}

/-- Abelian-group-valued sheaf composition exists on `(Spaces/X)_fppf`. -/
instance overFppfTopology_hasSheafCompose (X : AlgebraicSpace S) :
    (overFppfTopology X).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  sorry

/-- Abelian-group-valued weak sheafification exists on `(Spaces/X)_fppf`. -/
instance overFppfTopology_hasWeakSheafify (X : AlgebraicSpace S) :
    HasWeakSheafify (overFppfTopology X) AddCommGrpCat.{u} :=
  sorry

/-- On `(Spaces/X)_fppf`, sheafification equivalences are the locally bijective
morphisms. -/
instance overFppfTopology_wEqualsLocallyBijective (X : AlgebraicSpace S) :
    (overFppfTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  sorry

/-- Abelian-group-valued sheaf composition exists on every slice of
`(Spaces/X)_fppf`. -/
instance overFppfTopology_over_hasSheafCompose (X : AlgebraicSpace S) :
    ∀ U : Over X,
      ((overFppfTopology X).over U).HasSheafCompose
        (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  fun U ↦ GrothendieckTopology.HasSheafCompose.over
    (overFppfTopology X) (forget₂ RingCat.{u} AddCommGrpCat.{u}) U

/-- Abelian-group-valued weak sheafification exists on every slice of
`(Spaces/X)_fppf`. -/
instance overFppfTopology_over_hasWeakSheafify (X : AlgebraicSpace S) :
    ∀ U : Over X,
      HasWeakSheafify ((overFppfTopology X).over U) AddCommGrpCat.{u} :=
  sorry

/-- On every slice of `(Spaces/X)_fppf`, sheafification equivalences are the
locally bijective morphisms. -/
instance overFppfTopology_over_wEqualsLocallyBijective (X : AlgebraicSpace S) :
    ∀ U : Over X,
      ((overFppfTopology X).over U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Fppf

end

end
