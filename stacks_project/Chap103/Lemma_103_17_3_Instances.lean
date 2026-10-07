module

public import stacks_project.Chap96.Definition_96_11_1_QCoh

/-!
# Sheafification on the inherited fppf site

`SheafOfModules.IsFiniteLocallyFree` and finite presentation of `𝒪_X`-modules
need weak sheafification on the inherited fppf topology and on its slices.
The slice instances are the existing fppf ringed-site over-instances; this
module records the matching inherited-topology names and the missing top-level
instances.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} (X : GroupoidsOver S)

/-- Weak sheafification of abelian groups exists on the inherited fppf topology of
a category fibred in groupoids. -/
instance inheritedFppfTopology_hasWeakSheafify :
    HasWeakSheafify (inheritedFppfTopology X) AddCommGrpCat.{u} :=
  sorry

/-- On the inherited fppf topology of a category fibred in groupoids, sheafification
equivalences are the locally bijective morphisms. -/
instance inheritedFppfTopology_wEqualsLocallyBijective :
    (inheritedFppfTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  sorry

/-- Abelian-group-valued sheaf composition exists on every slice of the inherited
fppf topology of a category fibred in groupoids. -/
instance inheritedFppfTopology_over_hasSheafCompose :
    ∀ x : X.total, ((inheritedFppfTopology X).over x).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  hasSheafCompose_fppfRingedSite_over X

/-- Weak sheafification of abelian groups exists on every slice of the inherited
fppf topology of a category fibred in groupoids. -/
instance inheritedFppfTopology_over_hasWeakSheafify :
    ∀ x : X.total, HasWeakSheafify ((inheritedFppfTopology X).over x)
      AddCommGrpCat.{u} :=
  hasWeakSheafify_fppfRingedSite_over X

/-- On every slice of the inherited fppf topology of a category fibred in
groupoids, sheafification equivalences are the locally bijective morphisms. -/
instance inheritedFppfTopology_over_wEqualsLocallyBijective :
    ∀ x : X.total, ((inheritedFppfTopology X).over x).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  wEqualsLocallyBijective_fppfRingedSite_over X

end AlgebraicGeometry.GroupoidsOver
