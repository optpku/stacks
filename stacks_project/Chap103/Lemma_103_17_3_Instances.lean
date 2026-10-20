/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap96.Definition_96_11_1_QCoh
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Sheafification.Fppf

/-!
# Sheafification on the inherited fppf site

`SheafOfModules.IsFiniteLocallyFree` and finite presentation of `𝒪_X`-modules
need weak sheafification on the inherited fppf topology and on its slices.
The typed checks identify the shared inherited-fppf certificates and the
canonical fppf ringed-site slice instances.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} (X : GroupoidsOver S)

#check (AlgebraicGeometry.GroupoidsOver.inheritedFppfTopology_hasWeakSheafify X :
  HasWeakSheafify (inheritedFppfTopology X) AddCommGrpCat.{u})

#check (AlgebraicGeometry.GroupoidsOver.inheritedFppfTopology_wEqualsLocallyBijective X :
  (inheritedFppfTopology X).WEqualsLocallyBijective AddCommGrpCat.{u})

#check (AlgebraicGeometry.GroupoidsOver.hasSheafCompose_fppfRingedSite_over X :
  ∀ x : X.total, ((inheritedFppfTopology X).over x).HasSheafCompose
    (forget₂ RingCat.{u} AddCommGrpCat.{u}))

#check (AlgebraicGeometry.GroupoidsOver.hasWeakSheafify_fppfRingedSite_over X :
  ∀ x : X.total, HasWeakSheafify ((inheritedFppfTopology X).over x)
    AddCommGrpCat.{u})

#check (AlgebraicGeometry.GroupoidsOver.wEqualsLocallyBijective_fppfRingedSite_over X :
  ∀ x : X.total, ((inheritedFppfTopology X).over x).WEqualsLocallyBijective
    AddCommGrpCat.{u})

/-- Weak sheafification of abelian groups exists on every slice of the inherited
fppf topology of a category fibred in groupoids. -/
instance inheritedFppfTopology_over_hasWeakSheafify :
    ∀ x : X.total, HasWeakSheafify ((inheritedFppfTopology X).over x)
      AddCommGrpCat.{u} :=
  hasWeakSheafify_fppfRingedSite_over X

/-- Sheafification equivalences on every slice of the inherited fppf topology of
a category fibred in groupoids are exactly the locally bijective morphisms. -/
instance inheritedFppfTopology_over_wEqualsLocallyBijective :
    ∀ x : X.total, ((inheritedFppfTopology X).over x).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  wEqualsLocallyBijective_fppfRingedSite_over X

end AlgebraicGeometry.GroupoidsOver
