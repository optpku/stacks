module

public import ReasLib.CategoryTheory.Sites.Descent.Family.DescentDatum
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback functoriality on family descent data

A morphism of fixed-target families induces a pullback functor on descent-data categories.
When two morphisms have the same base map, the resulting pullback functors are canonically
isomorphic.

## Main declarations

* `CategoryTheory.DescentDatum.Pullback.functor` — pullback on descent data along a family morphism.
* `CategoryTheory.DescentDatum.Pullback.functor_obj_obj` — its action on local objects.
* `CategoryTheory.DescentDatum.Pullback.functor_map_hom` — its action on morphism components.
* `CategoryTheory.DescentDatum.Pullback.functor_obj_hom` — its action on descent comparisons.
* `CategoryTheory.DescentDatum.Pullback.functorOfHom` — the family-morphism specialization.
* `CategoryTheory.DescentDatum.Pullback.functorOfHom_obj_obj` — its object computation.
* `CategoryTheory.DescentDatum.Pullback.functorOfHom_map_hom` — its morphism computation.
* `CategoryTheory.DescentDatum.Pullback.functorOfHom_obj_hom` — its comparison computation.
* `CategoryTheory.DescentDatum.Pullback.functorOfRefinement` — the same-target specialization.
* `CategoryTheory.DescentDatum.Pullback.canonicalIsoOfHom` — canonical descent compatibility.
* `CategoryTheory.DescentDatum.Pullback.iso` — canonical iso for same-base morphisms.
* `CategoryTheory.DescentDatum.Pullback.isoOfHom` — its family-morphism specialization.
-/

@[expose] public section

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor Limits
open SemiRepresentableFamily.Over

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]
variable {p : S ⥤ C}
variable (hc : Functor.Cleavage p)

variable {U V : C}
variable (𝒰 : SemiRepresentableFamily.Over U)
variable (𝒱 : SemiRepresentableFamily.Over V)

/-- The pullback functor on descent data induced by a morphism of fixed-target families.
For families `𝒰 → U` and `𝒱 → V` with an index map `α`, a base morphism `h : U ⟶ V`, and
component maps compatible with `h`, this sends descent data on `𝒱` to descent data on `𝒰`. -/
@[stacks 02ZE "pullback functor on descent data"]
noncomputable abbrev DescentDatum.Pullback.functor
    {α : 𝒰.index → 𝒱.index}
    {h : U ⟶ V}
    (g : ∀ i, (𝒰.obj i).left ⟶ (𝒱.obj (α i)).left)
    (hg : ∀ i, g i ≫ (𝒱.obj (α i)).hom = (𝒰.obj i).hom ≫ h) :
    DescentDatum hc 𝒱 ⥤ DescentDatum hc 𝒰 :=
  Pseudofunctor.DescentData.pullFunctor hc.toPseudofunctor hg

/-- Pullback of a descent datum evaluates at `i` by reindexing its `α i` component along
`g i`. -/
@[simp, stacks 02ZE "pullback object component"]
theorem DescentDatum.Pullback.functor_obj_obj
    {α : 𝒰.index → 𝒱.index}
    {h : U ⟶ V}
    (g : ∀ i, (𝒰.obj i).left ⟶ (𝒱.obj (α i)).left)
    (hg : ∀ i, g i ≫ (𝒱.obj (α i)).hom = (𝒰.obj i).hom ≫ h)
    (D : DescentDatum hc 𝒱) (i : 𝒰.index) :
    ((DescentDatum.Pullback.functor hc 𝒰 𝒱 g hg).obj D).obj i =
      (hc.reindex (g i)).obj (D.obj (α i)) := sorry

/-- Pullback of a morphism of descent data evaluates at `i` by reindexing its `α i`
component along `g i`. -/
@[simp, stacks 02ZE "pullback morphism component"]
theorem DescentDatum.Pullback.functor_map_hom
    {α : 𝒰.index → 𝒱.index}
    {h : U ⟶ V}
    (g : ∀ i, (𝒰.obj i).left ⟶ (𝒱.obj (α i)).left)
    (hg : ∀ i, g i ≫ (𝒱.obj (α i)).hom = (𝒰.obj i).hom ≫ h)
    {D E : DescentDatum hc 𝒱} (φ : D ⟶ E) (i : 𝒰.index) :
    ((DescentDatum.Pullback.functor hc 𝒰 𝒱 g hg).map φ).hom i =
      (hc.reindex (g i)).map (φ.hom (α i)) := sorry

/-- The comparison morphism of a pulled-back descent datum is the canonical pullback of the
original comparison morphism to the compatible cone over `𝒰`. -/
@[stacks 02ZE "pullback descent comparison"]
theorem DescentDatum.Pullback.functor_obj_hom
    {α : 𝒰.index → 𝒱.index}
    {h : U ⟶ V}
    (g : ∀ i, (𝒰.obj i).left ⟶ (𝒱.obj (α i)).left)
    (hg : ∀ i, g i ≫ (𝒱.obj (α i)).hom = (𝒰.obj i).hom ≫ h)
    (D : DescentDatum hc 𝒱) {Y : C} (q : Y ⟶ U) {i j : 𝒰.index}
    (f₁ : Y ⟶ (𝒰.obj i).left) (f₂ : Y ⟶ (𝒰.obj j).left)
    (hf₁ : f₁ ≫ (𝒰.obj i).hom = q) (hf₂ : f₂ ≫ (𝒰.obj j).hom = q) :
    ((DescentDatum.Pullback.functor hc 𝒰 𝒱 g hg).obj D).hom q f₁ f₂ hf₁ hf₂ =
      Pseudofunctor.DescentData.pullFunctorObjHom
        (F := hc.toPseudofunctor)
        (f := fun k : 𝒱.index ↦ (𝒱.obj k).hom)
        (p := h)
        (f' := fun k : 𝒰.index ↦ (𝒰.obj k).hom)
        (α := α) (p' := g) hg D q f₁ f₂ hf₁ hf₂ := sorry

/-- The pullback functor on descent data induced by a morphism of fixed-target families over
`base`. This is the ergonomic form of `DescentDatum.Pullback.functor`: the compatibility with `base`
is read from the slice-category morphism. -/
@[stacks 02ZD "(2) family-morphism pullback functor"]
noncomputable abbrev DescentDatum.Pullback.functorOfHom
    {𝒰 : SemiRepresentableFamily.Over U}
    {𝒱 : SemiRepresentableFamily.Over V}
    {base : U ⟶ V}
    (φ : SemiRepresentableFamily.Over.map (Over.map base) 𝒰 ⟶ 𝒱) :
    DescentDatum hc 𝒱 ⥤ DescentDatum hc 𝒰 :=
  DescentDatum.Pullback.functor hc 𝒰 𝒱
    (fun i ↦ (φ.f i).left)
    (SemiRepresentableFamily.Over.Hom.map_hom base φ)

/-- The object component of the family-morphism pullback functor is reindexing along the component
map of the family morphism.  This is the source-facing form of the generic pullback computation. -/
@[simp, stacks 02ZD "(1) pulled-back descent datum"]
theorem DescentDatum.Pullback.functorOfHom_obj_obj
    {𝒰 : SemiRepresentableFamily.Over U}
    {𝒱 : SemiRepresentableFamily.Over V}
    {base : U ⟶ V}
    (φ : SemiRepresentableFamily.Over.map (Over.map base) 𝒰 ⟶ 𝒱)
    (D : DescentDatum hc 𝒱) (i : 𝒰.index) :
    ((DescentDatum.Pullback.functorOfHom hc φ).obj D).obj i =
      (hc.reindex (φ.f i).left).obj (D.obj (φ.α i)) := sorry

/-- The family-morphism pullback functor acts on a descent-data morphism by the corresponding
reindexed component.  This source-facing readout avoids expanding the underlying indexing map
and compatibility proof at each use site. -/
@[simp, stacks 02ZD "family-morphism pullback morphism component"]
theorem DescentDatum.Pullback.functorOfHom_map_hom
    {𝒰 : SemiRepresentableFamily.Over U}
    {𝒱 : SemiRepresentableFamily.Over V}
    {base : U ⟶ V}
    (φ : SemiRepresentableFamily.Over.map (Over.map base) 𝒰 ⟶ 𝒱)
    {D E : DescentDatum hc 𝒱} (η : D ⟶ E) (i : 𝒰.index) :
    ((DescentDatum.Pullback.functorOfHom hc φ).map η).hom i =
      (hc.reindex (φ.f i).left).map (η.hom (φ.α i)) := sorry

/-- The comparison morphism of a family-morphism pullback is the canonical pulled-back
comparison from the target descent datum. -/
@[simp, stacks 02ZD "family-morphism pullback comparison component"]
theorem DescentDatum.Pullback.functorOfHom_obj_hom
    {𝒰 : SemiRepresentableFamily.Over U}
    {𝒱 : SemiRepresentableFamily.Over V}
    {base : U ⟶ V}
    (φ : SemiRepresentableFamily.Over.map (Over.map base) 𝒰 ⟶ 𝒱)
    (D : DescentDatum hc 𝒱) {Y : C} (q : Y ⟶ U) {i j : 𝒰.index}
    (f₁ : Y ⟶ (𝒰.obj i).left) (f₂ : Y ⟶ (𝒰.obj j).left)
    (hf₁ : f₁ ≫ (𝒰.obj i).hom = q) (hf₂ : f₂ ≫ (𝒰.obj j).hom = q) :
    ((DescentDatum.Pullback.functorOfHom hc φ).obj D).hom q f₁ f₂ hf₁ hf₂ =
      Pseudofunctor.DescentData.pullFunctorObjHom
        (F := hc.toPseudofunctor)
        (f := fun k : 𝒱.index ↦ (𝒱.obj k).hom)
        (p := base)
        (f' := fun k : 𝒰.index ↦ (𝒰.obj k).hom)
        (α := φ.α) (p' := fun k ↦ (φ.f k).left)
        (w := SemiRepresentableFamily.Over.Hom.map_hom base φ)
        D q f₁ f₂ hf₁ hf₂ := sorry

/-- Pullback of descent data along a refinement of families with a common target. This is the
same-target interface to `DescentDatum.Pullback.functor`, so callers do not need to manufacture an
identity-base adapter. -/
@[stacks 02ZD "same-target family refinement pullback"]
noncomputable abbrev DescentDatum.Pullback.functorOfRefinement
    {T : C} {𝒰' 𝒱' : SemiRepresentableFamily.Over T}
    (φ : 𝒰' ⟶ 𝒱') :
    DescentDatum hc 𝒱' ⥤ DescentDatum hc 𝒰' :=
  DescentDatum.Pullback.functor hc 𝒰' 𝒱'
    (fun i ↦ (φ.f i).left) (SemiRepresentableFamily.Over.Hom.map_hom_id φ)

/-- Pullback of descent data along the identity refinement is canonically isomorphic to the
identity functor. -/
@[stacks 02ZE "identity law for family refinement pullback"]
noncomputable def DescentDatum.Pullback.functorOfRefinement.idIso
    {T : C} (𝒰' : SemiRepresentableFamily.Over T) :
    DescentDatum.Pullback.functorOfRefinement hc (𝟙 𝒰') ≅
      𝟭 (DescentDatum hc 𝒰') :=
  Pseudofunctor.DescentData.pullFunctorIdIso
    (F := hc.toPseudofunctor) (f := fun i : 𝒰'.index ↦ (𝒰'.obj i).hom) T

/-- Pullback of descent data along a composite refinement is canonically isomorphic to the
composite of the two pullback functors. -/
@[stacks 02ZE "composition law for family refinement pullback"]
noncomputable def DescentDatum.Pullback.functorOfRefinement.compIso
    {T : C} {𝒰' 𝒱' 𝒲' : SemiRepresentableFamily.Over T}
    (φ : 𝒰' ⟶ 𝒱') (ψ : 𝒱' ⟶ 𝒲') :
    DescentDatum.Pullback.functorOfRefinement hc ψ ⋙
        DescentDatum.Pullback.functorOfRefinement hc φ ≅
      DescentDatum.Pullback.functorOfRefinement hc (φ ≫ ψ) :=
  Pseudofunctor.DescentData.pullFunctorCompIso
    (F := hc.toPseudofunctor) (f := fun i : 𝒲'.index ↦ (𝒲'.obj i).hom)
    (p := 𝟙 T) (f' := fun i : 𝒱'.index ↦ (𝒱'.obj i).hom)
    (α := ψ.α) (p' := fun i ↦ (ψ.f i).left)
    (q := 𝟙 T) (f'' := fun i : 𝒰'.index ↦ (𝒰'.obj i).hom)
    (β := φ.α) (q' := fun i ↦ (φ.f i).left)
    (w := SemiRepresentableFamily.Over.Hom.map_hom_id ψ)
    (w' := SemiRepresentableFamily.Over.Hom.map_hom_id φ)
    (r := 𝟙 T) (r' := fun i ↦ ((φ ≫ ψ).f i).left)
    (hr := Category.id_comp _) (hr' := fun i ↦
      (SemiRepresentableFamily.Over.Hom.comp_left φ ψ i).symm)

/-- Canonical descent data commute with pullback along a morphism of fixed-target families.
The comparison identifies first forming the descent datum for `𝒱` and then pulling it back to
`𝒰` with first reindexing along the base map `h : U ⟶ V` and then forming the descent datum for
`𝒰`. -/
@[stacks 02ZE "canonical descent-data pullback comparison"]
noncomputable def DescentDatum.Pullback.canonicalIso
    {α : 𝒰.index → 𝒱.index}
    {h : U ⟶ V}
    (g : ∀ i, (𝒰.obj i).left ⟶ (𝒱.obj (α i)).left)
    (hg : ∀ i, g i ≫ (𝒱.obj (α i)).hom = (𝒰.obj i).hom ≫ h) :
    DescentDatum.canonicalFunctor hc 𝒱 ⋙ DescentDatum.Pullback.functor hc 𝒰 𝒱 g hg ≅
      hc.reindex h ⋙ DescentDatum.canonicalFunctor hc 𝒰 :=
  Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso hc.toPseudofunctor hg ≪≫
    Functor.isoWhiskerRight (Functor.Cleavage.toPseudofunctor.mapIso hc h)
      (DescentDatum.canonicalFunctor hc 𝒰)

/-- Canonical descent data commute with pullback along a morphism of fixed-target families.
This is the family-morphism form of `DescentDatum.Pullback.canonicalIso`. -/
@[stacks 02ZE "family-morphism canonical descent-data pullback comparison"]
noncomputable def DescentDatum.Pullback.canonicalIsoOfHom
    {𝒰 : SemiRepresentableFamily.Over U}
    {𝒱 : SemiRepresentableFamily.Over V}
    {base : U ⟶ V}
    (φ : SemiRepresentableFamily.Over.map (Over.map base) 𝒰 ⟶ 𝒱) :
    DescentDatum.canonicalFunctor hc 𝒱 ⋙
        DescentDatum.Pullback.functorOfHom hc (𝒰 := 𝒰) (𝒱 := 𝒱) φ ≅
      hc.reindex base ⋙ DescentDatum.canonicalFunctor hc 𝒰 :=
  DescentDatum.Pullback.canonicalIso hc 𝒰 𝒱
    (fun i ↦ (φ.f i).left)
    (SemiRepresentableFamily.Over.Hom.map_hom base φ)

/-- When two morphisms of fixed-target families have the same base map `h`, the resulting
pullback functors are canonically isomorphic. This justifies writing `h*` without specifying
the chosen lifts. -/
@[stacks 02ZE "same-base family pullback comparison"]
noncomputable def DescentDatum.Pullback.iso
    {α β : 𝒰.index → 𝒱.index}
    {h : U ⟶ V}
    (g : ∀ i, (𝒰.obj i).left ⟶ (𝒱.obj (α i)).left)
    (hg : ∀ i, g i ≫ (𝒱.obj (α i)).hom = (𝒰.obj i).hom ≫ h)
    (g' : ∀ i, (𝒰.obj i).left ⟶ (𝒱.obj (β i)).left)
    (hg' : ∀ i, g' i ≫ (𝒱.obj (β i)).hom = (𝒰.obj i).hom ≫ h) :
    DescentDatum.Pullback.functor hc 𝒰 𝒱 g hg ≅
      DescentDatum.Pullback.functor hc 𝒰 𝒱 g' hg' :=
  Pseudofunctor.DescentData.pullFunctorIso
    (F := hc.toPseudofunctor) (f := fun i : 𝒱.index ↦ (𝒱.obj i).hom)
    (p := h) (f' := fun i : 𝒰.index ↦ (𝒰.obj i).hom)
    (α := α) (p' := g) (w := hg) (β := β) (p'' := g') (w' := hg')

/-- The canonical isomorphism between pullback functors induced by two family morphisms with the
same base map. -/
@[stacks 02ZD "(3) same-base pullback-functor comparison"]
noncomputable def DescentDatum.Pullback.isoOfHom
    {𝒰 : SemiRepresentableFamily.Over U}
    {𝒱 : SemiRepresentableFamily.Over V}
    {base : U ⟶ V}
    (φ φ' : SemiRepresentableFamily.Over.map (Over.map base) 𝒰 ⟶ 𝒱) :
    DescentDatum.Pullback.functorOfHom hc (𝒰 := 𝒰) (𝒱 := 𝒱) φ ≅
      DescentDatum.Pullback.functorOfHom hc (𝒰 := 𝒰) (𝒱 := 𝒱) φ' :=
  DescentDatum.Pullback.iso hc 𝒰 𝒱
    (fun i ↦ (φ.f i).left)
    (SemiRepresentableFamily.Over.Hom.map_hom base φ)
    (fun i ↦ (φ'.f i).left)
    (SemiRepresentableFamily.Over.Hom.map_hom base φ')

/-- At a member `i`, the forward same-base comparison is the descent isomorphism between the
two chosen component maps from `𝒰.obj i`. -/
@[simp, stacks 02ZD "family-morphism pullback comparison component readout"]
theorem DescentDatum.Pullback.isoOfHom_hom_app_hom
    {𝒰 : SemiRepresentableFamily.Over U}
    {𝒱 : SemiRepresentableFamily.Over V}
    {base : U ⟶ V}
    (φ φ' : SemiRepresentableFamily.Over.map (Over.map base) 𝒰 ⟶ 𝒱)
    (D : DescentDatum hc 𝒱) (i : 𝒰.index) :
    ((DescentDatum.Pullback.isoOfHom hc φ φ').hom.app D).hom i =
      D.hom ((𝒰.obj i).hom ≫ base) (φ.f i).left (φ'.f i).left
        (SemiRepresentableFamily.Over.Hom.map_hom base φ i)
        (SemiRepresentableFamily.Over.Hom.map_hom base φ' i) := sorry

end CategoryTheory
