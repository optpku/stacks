/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import ReasLib.CategoryTheory.Sites.Precoverage.Continuous
public import ReasLib.CategoryTheory.Sites.Precoverage.CoverLifting
public import stacks_project.Chap07.Definition_7_6_2_Site
public import stacks_project.Chap85.Lemma_85_3_2_Total

/-!
# Slice diagram of a simplicial object of a site

A simplicial object `U` of a category `C` induces the simplicial object of slice
categories `n ↦ Over (U.obj n)`, with structure maps `Over.map`. Stage coverings
are the slice precoverages `(J.over (U.obj n)).toPrecoverage`.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The slice precoverage associated to a Grothendieck topology is a site when `C` has
fibre products. -/
instance over_toPrecoverage_isSite (X : C) [HasPullbacks C] :
    (J.over X).toPrecoverage.IsSite :=
  sorry

/-- Postcomposition `Over.map f` has property `P`: selected covers in `J.over Y` lift along
maps out of objects in the image, yielding selected covers in `J.over X`. -/
instance overMap_hasCoverLifts {X Y : C} (f : X ⟶ Y) [HasPullbacks C] :
    Functor.Precoverage.HasCoverLifts (Over.map f)
      (J.over X).toPrecoverage (J.over Y).toPrecoverage :=
  sorry

end CategoryTheory.GrothendieckTopology

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

/-- The simplicial object of slice categories `n ↦ Over (U.obj n)`, with structure maps
`Over.map (U.map φ)`. -/
abbrev sliceDiagram (U : SimplicialObject C) : SimplicialObject Cat.{v, max u v} :=
  U ⋙ Over.mapFunctor C

/-- The stage category of `sliceDiagram U` at `n` is `Over (U.obj n)`. -/
theorem sliceDiagram_obj (U : SimplicialObject C) (n : SimplexCategoryᵒᵖ) :
    (sliceDiagram U).obj n = Cat.of (Over (U.obj n)) :=
  sorry

/-- Structure maps of `sliceDiagram U` are postcomposition `Over.map (U.map φ)`. -/
theorem sliceDiagram_map (U : SimplicialObject C) {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    (sliceDiagram U).map φ = (Over.map (U.map φ)).toCatHom :=
  sorry

variable (J : GrothendieckTopology C)

/-- The stage precoverage on `Over (U.obj n)` induced by `J`. -/
def slicePrecoverage (U : SimplicialObject C) (n : SimplexCategoryᵒᵖ) :
    Precoverage ((sliceDiagram U).obj n) :=
  (J.over (U.obj n)).toPrecoverage

/-- A presieve covers in `slicePrecoverage J U n` iff the generated sieve covers for
`J.over (U.obj n)`. -/
theorem mem_slicePrecoverage_iff (U : SimplicialObject C) {n : SimplexCategoryᵒᵖ}
    {V : Over (U.obj n)} {R : Presieve V} :
    R ∈ slicePrecoverage J U n V ↔ Sieve.generate R ∈ J.over (U.obj n) V :=
  sorry

/-- Base change along a structure map `U.map φ` is continuous for the slice
precoverages. -/
instance sliceStructurePullback_isContinuous (U : SimplicialObject C) [HasPullbacks C]
    {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    Functor.Precoverage.IsContinuous (Over.pullback (U.map φ))
      (slicePrecoverage J U m) (slicePrecoverage J U n) :=
  sorry

/-- Structure maps of the slice sites compose up to the canonical `Over.pullbackComp`
isomorphism, rather than as a strict functor `SimplexCategory ⥤ Cat`. -/
noncomputable def sliceStructurePullback_compIso (U : SimplicialObject C) [HasPullbacks C]
    {n m k : SimplexCategoryᵒᵖ} (φ : n ⟶ m) (ψ : m ⟶ k) :
    Over.pullback (U.map (φ ≫ ψ)) ≅
      Over.pullback (U.map ψ) ⋙ Over.pullback (U.map φ) :=
  conjugateIsoEquiv
      (Over.mapPullbackAdj (U.map (φ ≫ ψ)))
      (Over.mapPullbackAdj (U.map φ ≫ U.map ψ))
      (Over.mapCongr (U.map φ ≫ U.map ψ) (U.map (φ ≫ ψ)) (U.map_comp φ ψ).symm) ≪≫
    Over.pullbackComp (U.map φ) (U.map ψ)

/-- `sliceStructurePullback_compIso` is the `Over.pullbackComp` comparison of the two
composites. -/
theorem sliceStructurePullback_compIso_eq (U : SimplicialObject C) [HasPullbacks C]
    {n m k : SimplexCategoryᵒᵖ} (φ : n ⟶ m) (ψ : m ⟶ k) :
    sliceStructurePullback_compIso U φ ψ =
      conjugateIsoEquiv
          (Over.mapPullbackAdj (U.map (φ ≫ ψ)))
          (Over.mapPullbackAdj (U.map φ ≫ U.map ψ))
          (Over.mapCongr (U.map φ ≫ U.map ψ) (U.map (φ ≫ ψ)) (U.map_comp φ ψ).symm) ≪≫
        Over.pullbackComp (U.map φ) (U.map ψ) :=
  sorry

/-- If `C` has fibre products, then `n ↦ C / U_n` is a simplicial object of sites: each
stage is a site and each `Over.map (U.map φ)` has property `P`. -/
instance sliceDiagram_isFiberwiseSite (U : SimplicialObject C) [HasPullbacks C] :
    Grothendieck.IsFiberwiseSite (sliceDiagram U) (slicePrecoverage J U) :=
  sorry

end CategoryTheory.SimplicialObject
