module

public import stacks_project.Chap90.Definition_90_22_1_Prorepresentable
public import stacks_project.Chap90.Definition_90_22_2_Completion
public import stacks_project.Chap90.Remark_90_7_11

/-!
# Completion–restriction comparison for groupoids in functors

The set-valued counit and unit lift to canonical isomorphisms of groupoids in
functors: restricting the completion of a groupoid on `ArtinianLocalAlgCat`
recovers it, and completing the restriction of a limit-preserving groupoid on
`CompleteLocalAlgCat` recovers it.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.GroupoidInFunctors

/-- The canonical isomorphism `restrictInclusion (completion G) ≅ G`, whose object
and arrow maps are the components of `Functor.typesCompletionCounitIso`. -/
def restrictInclusionCompletionIso
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k)) :
    Iso (restrictInclusion (completion G)) G where
  hom :=
    { obj := (Functor.typesCompletionCounitIso.app G.U).hom
      arrow := (Functor.typesCompletionCounitIso.app G.R).hom
      map_s := sorry
      map_t := sorry
      map_c := sorry }
  inv :=
    { obj := (Functor.typesCompletionCounitIso.app G.U).inv
      arrow := (Functor.typesCompletionCounitIso.app G.R).inv
      map_s := sorry
      map_t := sorry
      map_c := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The object map of `restrictInclusionCompletionIso G` is the counit at `G.U`. -/
theorem restrictInclusionCompletionIso_hom_obj
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k)) :
    (restrictInclusionCompletionIso G).hom.obj =
      Functor.typesCompletionCounit.app G.U :=
  sorry

/-- The arrow map of `restrictInclusionCompletionIso G` is the counit at `G.R`. -/
theorem restrictInclusionCompletionIso_hom_arrow
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k)) :
    (restrictInclusionCompletionIso G).hom.arrow =
      Functor.typesCompletionCounit.app G.R :=
  sorry

/-- The inverse object map of `restrictInclusionCompletionIso G` is the inverse
counit at `G.U`. -/
theorem restrictInclusionCompletionIso_inv_obj
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k)) :
    (restrictInclusionCompletionIso G).inv.obj =
      (Functor.typesCompletionCounitIso.app G.U).inv :=
  sorry

/-- The inverse arrow map of `restrictInclusionCompletionIso G` is the inverse
counit at `G.R`. -/
theorem restrictInclusionCompletionIso_inv_arrow
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k)) :
    (restrictInclusionCompletionIso G).inv.arrow =
      (Functor.typesCompletionCounitIso.app G.R).inv :=
  sorry

/-- The canonical isomorphism `completion (restrictInclusion G) ≅ G` when `G.U`
and `G.R` preserve limits. Representable object and arrow functors preserve
limits, so this applies in particular when those functors are representable. -/
def completionRestrictInclusionIso
    (G : GroupoidInFunctors.{u + 1, u, u} (CompleteLocalAlgCat Λ k))
    [PreservesLimits G.U] [PreservesLimits G.R] :
    Iso (completion (restrictInclusion G)) G where
  hom :=
    { obj := (asIso (Functor.typesCompletionUnit.app G.U)).inv
      arrow := (asIso (Functor.typesCompletionUnit.app G.R)).inv
      map_s := sorry
      map_t := sorry
      map_c := sorry }
  inv :=
    { obj := Functor.typesCompletionUnit.app G.U
      arrow := Functor.typesCompletionUnit.app G.R
      map_s := sorry
      map_t := sorry
      map_c := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The object map of `completionRestrictInclusionIso G` is the inverse unit at
`G.U`. -/
theorem completionRestrictInclusionIso_hom_obj
    (G : GroupoidInFunctors.{u + 1, u, u} (CompleteLocalAlgCat Λ k))
    [PreservesLimits G.U] [PreservesLimits G.R] :
    (completionRestrictInclusionIso G).hom.obj =
      inv (Functor.typesCompletionUnit.app G.U) :=
  sorry

/-- The arrow map of `completionRestrictInclusionIso G` is the inverse unit at
`G.R`. -/
theorem completionRestrictInclusionIso_hom_arrow
    (G : GroupoidInFunctors.{u + 1, u, u} (CompleteLocalAlgCat Λ k))
    [PreservesLimits G.U] [PreservesLimits G.R] :
    (completionRestrictInclusionIso G).hom.arrow =
      inv (Functor.typesCompletionUnit.app G.R) :=
  sorry

/-- The inverse object map of `completionRestrictInclusionIso G` is the unit at
`G.U`. -/
theorem completionRestrictInclusionIso_inv_obj
    (G : GroupoidInFunctors.{u + 1, u, u} (CompleteLocalAlgCat Λ k))
    [PreservesLimits G.U] [PreservesLimits G.R] :
    (completionRestrictInclusionIso G).inv.obj =
      Functor.typesCompletionUnit.app G.U :=
  sorry

/-- The inverse arrow map of `completionRestrictInclusionIso G` is the unit at
`G.R`. -/
theorem completionRestrictInclusionIso_inv_arrow
    (G : GroupoidInFunctors.{u + 1, u, u} (CompleteLocalAlgCat Λ k))
    [PreservesLimits G.U] [PreservesLimits G.R] :
    (completionRestrictInclusionIso G).inv.arrow =
      Functor.typesCompletionUnit.app G.R :=
  sorry

end CategoryTheory.GroupoidInFunctors
