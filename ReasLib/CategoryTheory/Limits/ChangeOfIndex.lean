module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Comparison maps for change of indexing category

A natural transformation to or from a reindexed diagram induces a comparison between the chosen
(co)limits without requiring the reindexed diagram itself to have a chosen (co)limit.  Leg
computations and naturality in both diagrams are exposed explicitly.
-/

@[expose] public section

universe vI uI vJ uJ vK uK vC uC

open CategoryTheory

namespace CategoryTheory.Limits

variable {I : Type uI} [Category.{vI} I]
variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C]
variable {H : I ⥤ J}

section Colimits

variable {M : I ⥤ C} [HasColimit M]
variable {N : J ⥤ C} [HasColimit N]

/-- The comparison from `colimit M` to `colimit N` induced by
`t : M ⟶ H ⋙ N`. -/
noncomputable def colimitComparison (t : M ⟶ H ⋙ N) :
    colimit M ⟶ colimit N :=
  colimit.desc M ((Cocone.precompose t).obj ((colimit.cocone N).whisker H))

/-- A colimit comparison commutes with each coprojection. -/
@[simp]
theorem colimitComparison.ι (t : M ⟶ H ⋙ N) (i : I) :
    colimit.ι M i ≫ colimitComparison t =
      t.app i ≫ colimit.ι N (H.obj i) := sorry

/-- A colimit comparison is the unique morphism satisfying its coprojection
equations. -/
@[stacks 002K]
theorem colimitComparison.existsUnique (t : M ⟶ H ⋙ N) :
    ∃! θ : colimit M ⟶ colimit N,
      ∀ i : I, colimit.ι M i ≫ θ =
        t.app i ≫ colimit.ι N (H.obj i) := sorry

/-- Colimit comparison is natural in the source diagram. -/
theorem colimitComparison.pre
    {M' : I ⥤ C} [HasColimit M'] (r : M' ⟶ M) (t : M ⟶ H ⋙ N) :
    colimitComparison (r ≫ t) = colimMap r ≫ colimitComparison t := sorry

/-- Colimit comparison is natural in the target diagram. -/
theorem colimitComparison.post
    {N' : J ⥤ C} [HasColimit N'] (t : M ⟶ H ⋙ N) (s : N ⟶ N') :
    colimitComparison (t ≫ Functor.whiskerLeft H s) =
      colimitComparison t ≫ colimMap s := sorry

end Colimits

section Limits

variable {M : I ⥤ C} [HasLimit M]
variable {N : J ⥤ C} [HasLimit N]

/-- The comparison from `limit N` to `limit M` induced by
`t : H ⋙ N ⟶ M`. -/
noncomputable def limitComparison (t : H ⋙ N ⟶ M) :
    limit N ⟶ limit M :=
  (limit.isLimit M).map ((limit.cone N).whisker H) t

/-- A limit comparison commutes with each projection. -/
@[simp]
theorem limitComparison.π (t : H ⋙ N ⟶ M) (i : I) :
    limitComparison t ≫ limit.π M i =
      limit.π N (H.obj i) ≫ t.app i := sorry

/-- A limit comparison is the unique morphism satisfying its projection
equations. -/
@[stacks 002L]
theorem limitComparison.existsUnique (t : H ⋙ N ⟶ M) :
    ∃! θ : limit N ⟶ limit M,
      ∀ i : I, θ ≫ limit.π M i =
        limit.π N (H.obj i) ≫ t.app i := sorry

/-- Limit comparison is natural in the target diagram. -/
theorem limitComparison.post
    {M' : I ⥤ C} [HasLimit M'] (t : H ⋙ N ⟶ M) (s : M ⟶ M') :
    limitComparison (t ≫ s) = limitComparison t ≫ limMap s := sorry

/-- Limit comparison is natural in the source diagram. -/
theorem limitComparison.pre
    {N' : J ⥤ C} [HasLimit N'] (r : N' ⟶ N) (t : H ⋙ N ⟶ M) :
    limitComparison (Functor.whiskerLeft H r ≫ t) =
      limMap r ≫ limitComparison t := sorry

end Limits

section ColimitFunctors

/-- Restricting diagrams along `H` induces a natural map from colimits over `I` to colimits over
`J`. -/
noncomputable def colimitPreNat (H : I ⥤ J)
    [HasColimitsOfShape I C] [HasColimitsOfShape J C] :
    (Functor.whiskeringLeft I J C).obj H ⋙
        (colim : (I ⥤ C) ⥤ C) ⟶
      (colim : (J ⥤ C) ⥤ C) :=
  NatTrans.mk
    (fun N ↦ colimit.pre N H)
    sorry

/-- The component of `colimitPreNat` is the standard comparison map `colimit.pre`. -/
@[simp]
theorem colimitPreNat.app (H : I ⥤ J)
    [HasColimitsOfShape I C] [HasColimitsOfShape J C] (N : J ⥤ C) :
    (colimitPreNat H).app N = colimit.pre N H := sorry

/-- Restriction along the identity indexing functor agrees with the map induced by the left
unitor of the diagram. -/
theorem colimitPreNat.id_app [HasColimitsOfShape I C] (M : I ⥤ C) :
    (colimitPreNat (𝟭 I)).app M =
      colim.map (Functor.leftUnitor M).hom := sorry

/-- Restriction of colimits along a composite indexing functor is the composite of the two
restriction maps. -/
theorem colimitPreNat.comp_app
    {K : Type uK} [Category.{vK} K] (H : I ⥤ J) (G : J ⥤ K)
    [HasColimitsOfShape I C] [HasColimitsOfShape J C]
    [HasColimitsOfShape K C] (N : K ⥤ C) :
    (colimitPreNat H).app (G ⋙ N) ≫ (colimitPreNat G).app N =
      (colimitPreNat (H ⋙ G)).app N := sorry

end ColimitFunctors

section LimitFunctors

/-- Restricting diagrams along `H` induces a natural map from limits over `J` to limits over
`I`. -/
noncomputable def limitPreNat (H : I ⥤ J)
    [HasLimitsOfShape I C] [HasLimitsOfShape J C] :
    (lim : (J ⥤ C) ⥤ C) ⟶
      (Functor.whiskeringLeft I J C).obj H ⋙
        (lim : (I ⥤ C) ⥤ C) :=
  NatTrans.mk
    (fun N ↦ limit.pre N H)
    sorry

/-- The component of `limitPreNat` is the standard comparison map `limit.pre`. -/
@[simp]
theorem limitPreNat.app (H : I ⥤ J)
    [HasLimitsOfShape I C] [HasLimitsOfShape J C] (N : J ⥤ C) :
    (limitPreNat H).app N = limit.pre N H := sorry

/-- Restriction along the identity indexing functor agrees with the map induced by the inverse
left unitor of the diagram. -/
theorem limitPreNat.id_app [HasLimitsOfShape I C] (M : I ⥤ C) :
    (limitPreNat (𝟭 I)).app M =
      lim.map (Functor.leftUnitor M).inv := sorry

/-- Restriction of limits along a composite indexing functor is the composite of the two
restriction maps. -/
theorem limitPreNat.comp_app
    {K : Type uK} [Category.{vK} K] (H : I ⥤ J) (G : J ⥤ K)
    [HasLimitsOfShape I C] [HasLimitsOfShape J C]
    [HasLimitsOfShape K C] (N : K ⥤ C) :
    (limitPreNat G).app N ≫ (limitPreNat H).app (G ⋙ N) =
      (limitPreNat (H ⋙ G)).app N := sorry

end LimitFunctors

end CategoryTheory.Limits
