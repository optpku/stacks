/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Basic
public import Mathlib.CategoryTheory.Sites.Equivalence

/-!
# Sheaves on the small Zariski site

The category of open subschemes of a scheme is equivalent to its full small Zariski site.
Transporting the usual open-cover topology across this equivalence identifies sheaves on the
small Zariski site with sheaves on the underlying topological space.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped TopCat

noncomputable section

universe u v w

namespace AlgebraicGeometry
namespace Scheme

variable (S : Scheme.{u})

/-- A morphism between open immersions over `S` induces the inclusion between their open
ranges. -/
def smallZariskiRangeMap {U V : S.smallZariskiSite} (f : U ⟶ V) :
    (@Scheme.Hom.opensRange U.left S ((smallZariskiForget S).obj U).hom U.prop) ⟶
      (@Scheme.Hom.opensRange V.left S ((smallZariskiForget S).obj V).hom V.prop) :=
  homOfLE <| by
    change Set.range ((smallZariskiForget S).obj U).hom ⊆
      Set.range ((smallZariskiForget S).obj V).hom
    have h := Over.w ((smallZariskiForget S).map f)
    rw [← h]
    simpa only [Scheme.Hom.comp_base, TopCat.coe_comp, ContinuousMap.coe_comp] using
      Set.range_comp_subset_range (f := ((smallZariskiForget S).map f).left)
        (g := ((smallZariskiForget S).obj V).hom)

/-- The open-range map associated to an identity morphism is the identity inclusion. -/
theorem smallZariskiRangeMap_id (U : S.smallZariskiSite) :
    smallZariskiRangeMap S (𝟙 U) = 𝟙 _ := sorry

/-- The open-range map associated to a composite is the composite of the open-range maps. -/
theorem smallZariskiRangeMap_comp {U V W : S.smallZariskiSite}
    (f : U ⟶ V) (g : V ⟶ W) :
    smallZariskiRangeMap S (f ≫ g) =
      smallZariskiRangeMap S f ≫ smallZariskiRangeMap S g := sorry

/-- The functor from the small Zariski site of `S` to its category of open subsets, sending an
open immersion to its open range. -/
def smallZariskiRangeFunctor : S.smallZariskiSite ⥤ S.Opens where
  obj U := @Scheme.Hom.opensRange U.left S ((smallZariskiForget S).obj U).hom U.prop
  map f := smallZariskiRangeMap S f
  map_id U := smallZariskiRangeMap_id S U
  map_comp f g := smallZariskiRangeMap_comp S f g

/-- The canonical isomorphism from an open subset of `S` to the range of its open-subscheme
inclusion. -/
def smallZariskiOpenUnitIsoApp (U : S.Opens) :
    U ≅ (smallZariskiOpenFunctor S ⋙ smallZariskiRangeFunctor S).obj U := by
  change U ≅ @Scheme.Hom.opensRange _ _ U.ι inferInstance
  exact eqToIso (Scheme.Opens.opensRange_ι (U := U)).symm

/-- The components of the open-range unit commute with inclusions of open subsets. -/
theorem smallZariskiOpenUnitIso_naturality {U V : S.Opens} (f : U ⟶ V) :
    f ≫ (smallZariskiOpenUnitIsoApp S V).hom =
      (smallZariskiOpenUnitIsoApp S U).hom ≫
        (smallZariskiOpenFunctor S ⋙ smallZariskiRangeFunctor S).map f := sorry

/-- The identity functor on the opens of `S` is naturally isomorphic to restriction followed by
open range. -/
def smallZariskiOpenUnitIso :
    Functor.id S.Opens ≅ smallZariskiOpenFunctor S ⋙ smallZariskiRangeFunctor S :=
  NatIso.ofComponents (smallZariskiOpenUnitIsoApp S)
    (smallZariskiOpenUnitIso_naturality S)

/-- The canonical isomorphism from the open subscheme associated to the range of an open
immersion over `S` to that open immersion. -/
def smallZariskiOpenCounitIsoApp (U : S.smallZariskiSite) :
    (smallZariskiRangeFunctor S ⋙ smallZariskiOpenFunctor S).obj U ≅ U := by
  refine MorphismProperty.Over.isoMk
    (@Scheme.Hom.isoOpensRange U.left S ((smallZariskiForget S).obj U).hom U.prop).symm ?_
  change (@Scheme.Hom.isoOpensRange U.left S
      ((smallZariskiForget S).obj U).hom U.prop).inv ≫ U.hom =
    ((smallZariskiOpenFunctor S).obj
      (@Scheme.Hom.opensRange U.left S
        ((smallZariskiForget S).obj U).hom U.prop)).hom
  rw [smallZariskiOpenFunctor_obj_hom]
  exact @Scheme.Hom.isoOpensRange_inv_comp U.left S
    ((smallZariskiForget S).obj U).hom U.prop

/-- The components of the open-range counit commute with morphisms of open immersions over
`S`. -/
theorem smallZariskiOpenCounitIso_naturality {U V : S.smallZariskiSite} (f : U ⟶ V) :
    (smallZariskiRangeFunctor S ⋙ smallZariskiOpenFunctor S).map f ≫
        (smallZariskiOpenCounitIsoApp S V).hom =
      (smallZariskiOpenCounitIsoApp S U).hom ≫ f := sorry

/-- Restriction after taking the open range is naturally isomorphic to the identity functor on
the small Zariski site of `S`. -/
def smallZariskiOpenCounitIso :
    smallZariskiRangeFunctor S ⋙ smallZariskiOpenFunctor S ≅
      Functor.id S.smallZariskiSite :=
  NatIso.ofComponents (smallZariskiOpenCounitIsoApp S)
    (smallZariskiOpenCounitIso_naturality S)

/-- Open subsets of `S` are equivalent to open immersions into `S`. -/
def smallZariskiOpenEquivalence : S.Opens ≌ S.smallZariskiSite :=
  CategoryTheory.Equivalence.mk (smallZariskiOpenFunctor S) (smallZariskiRangeFunctor S)
    (smallZariskiOpenUnitIso S) (smallZariskiOpenCounitIso S)

/-- The canonical functor from open subsets of `S` to its small Zariski site is an equivalence. -/
instance smallZariskiOpenFunctor_isEquivalence :
    (smallZariskiOpenFunctor S).IsEquivalence :=
  Functor.IsEquivalence.mk' (smallZariskiRangeFunctor S)
    (smallZariskiOpenUnitIso S) (smallZariskiOpenCounitIso S)

/-- A sieve of open subsets of `S` is covering exactly when its pushforward to the small
Zariski site is covering. -/
theorem smallZariskiOpenFunctor_functorPushforward_mem_iff
    {U : S.Opens} {R : Sieve U} :
    R.functorPushforward (smallZariskiOpenFunctor S) ∈
          S.smallZariskiTopology ((smallZariskiOpenFunctor S).obj U) ↔
      R ∈ Opens.grothendieckTopology (S : TopCat) U := sorry

/-- The canonical functor from open subsets of `S` identifies the usual open-cover topology with
the topology on the small Zariski site. -/
instance smallZariskiOpenFunctor_isDenseSubsite :
    (smallZariskiOpenFunctor S).IsDenseSubsite
      (Opens.grothendieckTopology (S : TopCat)) S.smallZariskiTopology where
  isCoverDense' :=
    { is_cover := fun U ↦ by
        convert! S.smallZariskiTopology.top_mem U
        ext Y f
        simp only [Sieve.top_apply, iff_true]
        exact ⟨
          { obj := (smallZariskiRangeFunctor S).obj Y
            lift := (smallZariskiOpenCounitIso S).inv.app Y
            map := (smallZariskiOpenCounitIso S).hom.app Y ≫ f
            fac := (smallZariskiOpenCounitIso S).inv_hom_id_app_assoc Y f }⟩ }
  isLocallyFull' :=
    { functorPushforward_imageSieve_mem := fun f ↦ by
        let hFF : (smallZariskiOpenFunctor S).FullyFaithful := by
          change (smallZariskiOpenEquivalence S).functor.FullyFaithful
          exact (smallZariskiOpenEquivalence S).fullyFaithfulFunctor
        rw [← hFF.map_preimage f]
        simp only [Functor.imageSieve_map, Sieve.functorPushforward_top,
          GrothendieckTopology.top_mem] }
  isLocallyFaithful' :=
    { functorPushforward_equalizer_mem := fun f₁ f₂ e ↦ by
        let hFF : (smallZariskiOpenFunctor S).FullyFaithful := by
          change (smallZariskiOpenEquivalence S).functor.FullyFaithful
          exact (smallZariskiOpenEquivalence S).fullyFaithfulFunctor
        obtain rfl := hFF.map_injective e
        simp }
  functorPushforward_mem_iff :=
    smallZariskiOpenFunctor_functorPushforward_mem_iff S

/-- The inverse functor of the symmetric open-subscheme equivalence identifies the usual
open-cover topology with the small Zariski topology. -/
instance smallZariskiOpenEquivalence_symm_inverse_isDenseSubsite :
    (smallZariskiOpenEquivalence S).symm.inverse.IsDenseSubsite
      (Opens.grothendieckTopology (S : TopCat)) S.smallZariskiTopology := by
  change (smallZariskiOpenFunctor S).IsDenseSubsite
    (Opens.grothendieckTopology (S : TopCat)) S.smallZariskiTopology
  exact smallZariskiOpenFunctor_isDenseSubsite S

/-- For any coefficient category, sheaves on the small Zariski site of `S` are equivalent to
sheaves on the underlying topological space of `S`. -/
def smallZariskiSheafEquiv (A : Type w) [Category.{v} A] :
    Sheaf S.smallZariskiTopology A ≌
      TopCat.Sheaf A (S.toPresheafedSpace : TopCat) :=
  (smallZariskiOpenEquivalence S).symm.sheafCongr S.smallZariskiTopology
    (Opens.grothendieckTopology (S : TopCat)) A

/-- Sheaves of types on the small Zariski site of `S` are equivalent to sheaves of types on its
underlying topological space. -/
def smallZariskiTypeSheafEquiv :
    Sheaf S.smallZariskiTopology (Type v) ≌
      TopCat.Sheaf (Type v) (S.toPresheafedSpace : TopCat) :=
  smallZariskiSheafEquiv S (Type v)

end Scheme
end AlgebraicGeometry
