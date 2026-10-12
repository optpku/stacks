/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.TopologyComparison
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.LowerShriek
public import ReasLib.CategoryTheory.Sites.Over.Abelian
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import ReasLib.CategoryTheory.Sites.Topos.ContinuousLeftAdjoint
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.Functor.Exactness.Composition
public import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Sheaf functors for a comparison of topologies

For `τ' ≤ τ`, this leaf owns the identity-site direct and inverse image functors between the
localized sheaf categories.  The underlying topology comparison is independent of any chapter;
derived-category constructions can import this leaf and build their own bounded or unbounded
derived models on top of the canonical functors.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w u v

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]
variable {τ τ' : GrothendieckTopology C}

/-- The localized topology order is inherited on every slice category. -/
@[stacks 0EZ3 "localized topology comparison on slices"]
theorem comparisonOver_le (hle : τ' ≤ τ) (X : C) : τ'.over X ≤ τ.over X := sorry

/-- The identity on `Over X` is continuous from the finer localized topology to the coarser one. -/
@[stacks 0EZ3 "localized topology comparison continuity"]
theorem comparisonOver_id_isContinuous
    (hle : τ' ≤ τ) (X : C) :
    Functor.IsContinuous (𝟭 (Over X)) (τ'.over X) (τ.over X) := sorry

/-- The identity on `Over X` is cocontinuous in the opposite direction. -/
@[stacks 0EZ3 "localized topology comparison cocontinuity"]
theorem comparisonOver_id_isCocontinuous
    (hle : τ' ≤ τ) (X : C) :
    Functor.IsCocontinuous (𝟭 (Over X)) (τ.over X) (τ'.over X) := sorry

section PullbackSupport

variable {A : Type w} [Category A]

/-- The identity on `Over X` admits pointwise left Kan extensions for every coefficient functor. -/
@[stacks 0EZ3 "identity slice pointwise left Kan extensions"]
instance comparisonTopologyPullbackHasPointwiseLeftKanExtension
    (X : C) (F : (Over X)ᵒᵖ ⥤ A) :
    ((𝟭 (Over X)).op).HasPointwiseLeftKanExtension F := sorry

/-- The identity on `Over X` admits left Kan extensions for every coefficient functor. -/
@[stacks 0EZ3 "identity slice left Kan extensions"]
instance comparisonTopologyPullbackHasLeftKanExtension
    (X : C) (F : (Over X)ᵒᵖ ⥤ A) :
    ((𝟭 (Over X)).op).HasLeftKanExtension F := sorry

/-- The continuous direct image `ε_{X,*}` for a topology comparison. -/
@[stacks 0EZ3 "topology comparison direct image"]
noncomputable abbrev comparisonTopologyPushforward
    (A : Type w) [Category A] (hle : τ' ≤ τ) (X : C) :
    Sheaf (τ.over X) A ⥤ Sheaf (τ'.over X) A :=
  -- The continuity proof depends on the supplied order `hle`; keep it scoped to this canonical
  -- comparison rather than registering an order-indexed global instance.
  let _ : Functor.IsContinuous (𝟭 (Over X)) (τ'.over X) (τ.over X) :=
    comparisonOver_id_isContinuous hle X
  (𝟭 (Over X)).sheafPushforwardContinuous A (τ'.over X) (τ.over X)

/-- The inverse image `ε_X⁻¹` for a topology comparison. -/
@[stacks 0EZ3 "topology comparison inverse image"]
noncomputable abbrev comparisonTopologyPullback
    (A : Type w) [Category A] (hle : τ' ≤ τ) (X : C)
    [HasWeakSheafify (τ.over X) A] :
    Sheaf (τ'.over X) A ⥤ Sheaf (τ.over X) A :=
  -- Both pins are presentation data for the continuous sheaf adjunction and depend on `hle`.
  let _ : Functor.IsContinuous (𝟭 (Over X)) (τ'.over X) (τ.over X) :=
    comparisonOver_id_isContinuous hle X
  let _ :
      ((𝟭 (Over X)).sheafPushforwardContinuous A
        (τ'.over X) (τ.over X)).IsRightAdjoint :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (𝟭 (Over X)) A (τ'.over X) (τ.over X)).isRightAdjoint
  (𝟭 (Over X)).sheafPullback A (τ'.over X) (τ.over X)

/-- Reusable notation for the inverse image in a comparison `τ' ≤ τ` on the slice over `X`. -/
scoped[GrothendieckTopology] notation "ε[" hle "]_(" X ")⁻¹" =>
  GrothendieckTopology.comparisonTopologyPullback _ hle X

/-- The canonical topology-comparison adjunction `ε_X⁻¹ ⊣ ε_{X,*}`. -/
@[stacks 0EZ3 "topology comparison adjunction"]
noncomputable abbrev comparisonTopologyAdjunction
    (A : Type w) [Category A] (hle : τ' ≤ τ) (X : C)
    [HasWeakSheafify (τ.over X) A] :
    comparisonTopologyPullback A hle X ⊣ comparisonTopologyPushforward A hle X :=
  -- The identity functor's continuity is order-indexed, so it must remain local to this adjunction.
  let _ : Functor.IsContinuous (𝟭 (Over X)) (τ'.over X) (τ.over X) :=
    comparisonOver_id_isContinuous hle X
  (𝟭 (Over X)).sheafAdjunctionContinuous A (τ'.over X) (τ.over X)

section Relocalization

variable {A : Type w} [Category A]

/-- The canonical underived square for a slice map and a topology comparison.

For `f : X ⟶ Y` and `τ' ≤ τ`, this is the composition comparison
`f_τ⁻¹ ⋙ ε_X ≅ ε_Y ⋙ f_{τ'}⁻¹`.  Its orientation is chosen for direct use as the
left-adjoint square in `CategoryTheory.DerivedBaseChange.map`. -/
@[stacks 0EZ3 "topology-comparison relocalization square"]
noncomputable def overMapComparison
    (hle : τ' ≤ τ) {X Y : C} (f : X ⟶ Y) :
    τ.overMapPullback A f ⋙ comparisonTopologyPushforward A hle X ≅
      comparisonTopologyPushforward A hle Y ⋙ τ'.overMapPullback A f :=
  -- These three continuity witnesses are the canonical square's geometric certificates; exposing
  -- them globally would create overlapping instances for every topology order and slice map.
  let _ : Functor.IsContinuous (𝟭 (Over X)) (τ'.over X) (τ.over X) :=
    comparisonOver_id_isContinuous hle X
  let _ : Functor.IsContinuous (𝟭 (Over Y)) (τ'.over Y) (τ.over Y) :=
    comparisonOver_id_isContinuous hle Y
  let _ : (Over.map f).IsContinuous (τ'.over X) (τ.over Y) :=
    Functor.isContinuous_comp (𝟭 (Over X)) (Over.map f) (τ'.over X) (τ.over X) (τ.over Y)
  (Functor.sheafPushforwardContinuousComp'
      (Functor.leftUnitor (Over.map f)) A
      (τ'.over X) (τ.over X) (τ.over Y)) ≪≫
    (Functor.sheafPushforwardContinuousComp'
      (Functor.rightUnitor (Over.map f)) A
      (τ'.over X) (τ'.over Y) (τ.over Y)).symm

/-- The mate of `overMapComparison` along the two topology-comparison adjunctions.

It is the canonical natural transformation
`f_{τ'}⁻¹ ⋙ ε_X⁻¹ ⟶ ε_Y⁻¹ ⋙ f_τ⁻¹` between inverse-image functors. -/
@[stacks 0EZ3 "topology-comparison inverse-image square"]
noncomputable def overMapPullbackComparison
    (hle : τ' ≤ τ) {X Y : C} (f : X ⟶ Y)
    [HasWeakSheafify (τ.over X) A] [HasWeakSheafify (τ.over Y) A] :
    τ'.overMapPullback A f ⋙ comparisonTopologyPullback A hle X ⟶
      comparisonTopologyPullback A hle Y ⋙ τ.overMapPullback A f :=
  DerivedBaseChange.mapOfRight
    (comparisonTopologyAdjunction A hle Y)
    (comparisonTopologyAdjunction A hle X)
    (TwoSquare.mk
      (comparisonTopologyPushforward A hle Y)
      (τ.overMapPullback A f)
      (τ'.overMapPullback A f)
      (comparisonTopologyPushforward A hle X)
      (overMapComparison (A := A) hle f).inv)

/-- The topology-comparison inverse-image square is pointwise invertible. -/
@[stacks 0EZ3 "topology-comparison inverse-image square isomorphism", instance]
instance overMapPullbackComparison_isIso
    (hle : τ' ≤ τ) {X Y : C} (f : X ⟶ Y)
    [HasWeakSheafify (τ.over X) A] [HasWeakSheafify (τ.over Y) A] :
    IsIso (overMapPullbackComparison (A := A) hle f) := sorry

/-- The canonical inverse-image square for relocalization and a topology comparison. -/
@[stacks 0EZ3 "topology-comparison inverse-image square isomorphism"]
noncomputable def overMapPullbackComparisonIso
    (hle : τ' ≤ τ) {X Y : C} (f : X ⟶ Y)
    [HasWeakSheafify (τ.over X) A] [HasWeakSheafify (τ.over Y) A] :
    τ'.overMapPullback A f ⋙ comparisonTopologyPullback A hle X ≅
      comparisonTopologyPullback A hle Y ⋙ τ.overMapPullback A f :=
  asIso (overMapPullbackComparison (A := A) hle f)

end Relocalization

/-- A sheaf for the coarser topology whose underlying presheaf also satisfies the finer
topology is canonically isomorphic to its topology-comparison inverse image.  The isomorphism
uses the explicit identity left-Kan extension and sheafification models, so its morphism data
does not come from choosing an isomorphism out of an `IsIsomorphic` proposition. -/
@[stacks 0EZ3 "finer sheaf as topology-comparison inverse image"]
noncomputable def comparisonTopologyPullbackIsoOfIsSheaf
    (A : Type w) [Category A] (hle : τ' ≤ τ) (X : C)
    [HasWeakSheafify (τ.over X) A]
    (F : Sheaf (τ'.over X) A) (hF : Presheaf.IsSheaf (τ.over X) F.1) :
    ((comparisonTopologyPullback A hle X).obj F) ≅
      (⟨F.1, hF⟩ : Sheaf (τ.over X) A) :=
  letI : Functor.IsContinuous (Functor.id (Over X)) (τ'.over X) (τ.over X) :=
    comparisonOver_id_isContinuous hle X
  letI :
      ((Functor.id (Over X)).sheafPushforwardContinuous A
        (τ'.over X) (τ.over X)).IsRightAdjoint :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Functor.id (Over X)) A (τ'.over X) (τ.over X)).isRightAdjoint
  (Functor.sheafPullbackConstruction.sheafPullbackIso
      (Functor.id (Over X)) A (τ'.over X) (τ.over X)).app F ≪≫
    (presheafToSheaf (τ.over X) A).mapIso
      ((((Functor.id (Over X)).op.lanAdjunction A).leftAdjointUniq
        Adjunction.id).app F.1) ≪≫
    (sheafificationIso (⟨F.1, hF⟩ : Sheaf (τ.over X) A)).symm

/-- The comparison-adjunction unit is the direct image of the inverse of
`comparisonTopologyPullbackIsoOfIsSheaf`.  This specification lets downstream proofs rewrite
the canonical unit without unfolding the identity Kan extension or sheafification models. -/
@[stacks 0EZ3 "topology-comparison unit specification on finer sheaves"]
theorem comparisonTopology_unit_app_eq_pullbackIso_inv
    (A : Type w) [Category A] (hle : τ' ≤ τ) (X : C)
    [HasWeakSheafify (τ.over X) A]
    (F : Sheaf (τ'.over X) A) (hF : Presheaf.IsSheaf (τ.over X) F.1) :
    (comparisonTopologyAdjunction A hle X).unit.app F =
      (comparisonTopologyPushforward A hle X).map
        (comparisonTopologyPullbackIsoOfIsSheaf A hle X F hF).inv := sorry

/-- The topology-comparison adjunction unit is invertible on a `τ'`-sheaf whose underlying
presheaf also satisfies the finer `τ`-sheaf condition. -/
@[stacks 0EZ3 "topology comparison unit isomorphism on finer sheaves"]
theorem comparisonTopology_unit_isIso_of_isSheaf
    (A : Type w) [Category A] (hle : τ' ≤ τ) (X : C)
    [HasWeakSheafify (τ.over X) A]
    (ℱ : Sheaf (τ'.over X) A)
    (hℱ : Presheaf.IsSheaf (τ.over X) ℱ.1) :
    IsIso ((comparisonTopologyAdjunction A hle X).unit.app ℱ) := sorry

end PullbackSupport

section Abelian

variable {A : Type w} [Category A]

/-- The topology-comparison direct image on abelian sheaves. -/
@[stacks 0EZ3 "abelian topology comparison direct image"]
noncomputable abbrev comparisonTopologyPushforwardAb
    (hle : τ' ≤ τ) (X : C) :
    Sheaf (τ.over X) AddCommGrpCat.{max u v} ⥤
      Sheaf (τ'.over X) AddCommGrpCat.{max u v} :=
  comparisonTopologyPushforward AddCommGrpCat.{max u v} hle X

/-- The topology-comparison inverse image on abelian sheaves. -/
@[stacks 0EZ3 "abelian topology comparison inverse image"]
noncomputable abbrev comparisonTopologyPullbackAb
    (hle : τ' ≤ τ) (X : C)
    [HasWeakSheafify (τ.over X) AddCommGrpCat.{max u v}] :
    Sheaf (τ'.over X) AddCommGrpCat.{max u v} ⥤
      Sheaf (τ.over X) AddCommGrpCat.{max u v} :=
  comparisonTopologyPullback AddCommGrpCat.{max u v} hle X

/-- The abelian topology-comparison direct image is additive. -/
@[stacks 0EZ3 "abelian topology comparison direct image additive", instance]
instance comparisonTopologyPushforwardAb_additive
    (hle : τ' ≤ τ) (X : C) :
    Functor.Additive (comparisonTopologyPushforwardAb hle X) := sorry

/-- The abelian topology-comparison inverse image is additive. -/
@[stacks 0EZ3 "abelian topology comparison inverse image additive", instance]
instance comparisonTopologyPullbackAb_additive
    (hle : τ' ≤ τ) (X : C)
    [HasSheafify (τ.over X) AddCommGrpCat.{max u v}] :
    Functor.Additive (comparisonTopologyPullbackAb hle X) := sorry

/-- The abelian topology-comparison inverse image preserves finite limits. -/
@[stacks 0EZ3 "abelian topology comparison finite limits", instance]
instance comparisonTopologyPullbackAb_preservesFiniteLimits
    (hle : τ' ≤ τ) (X : C)
    [HasSheafify (τ.over X) AddCommGrpCat.{max u v}] :
    PreservesFiniteLimits (comparisonTopologyPullbackAb hle X) := sorry

/-- The abelian topology-comparison inverse image preserves finite colimits. -/
@[stacks 0EZ3 "abelian topology comparison finite colimits", instance]
instance comparisonTopologyPullbackAb_preservesFiniteColimits
    (hle : τ' ≤ τ) (X : C)
    [HasSheafify (τ.over X) AddCommGrpCat.{max u v}] :
    PreservesFiniteColimits (comparisonTopologyPullbackAb hle X) := sorry

/-- The exact-functor owner for topology-comparison inverse image on abelian sheaves. -/
@[stacks 0EZ3 "exact topology-comparison inverse image"]
noncomputable abbrev comparisonTopologyPullbackAbExact
    (hle : τ' ≤ τ) (X : C)
    [HasSheafify (τ.over X) AddCommGrpCat.{max u v}] :
    Sheaf (τ'.over X) AddCommGrpCat.{max u v} ⥤ₑ
      Sheaf (τ.over X) AddCommGrpCat.{max u v} :=
  ExactFunctor.of (comparisonTopologyPullbackAb hle X)

/-- The topology-comparison direct image preserves injectives because its left adjoint is exact.
This is a canonical Prop instance, so downstream derived-sections APIs do not need to rebuild the
same adjunction consequence at every use site. -/
@[stacks 0EZ3 "abelian topology-comparison direct image preserves injectives", instance]
instance comparisonTopologyPushforwardAb_preservesInjectiveObjects
    (hle : τ' ≤ τ) (X : C)
    [HasSheafify (τ.over X) AddCommGrpCat.{max u v}] :
    (comparisonTopologyPushforwardAb hle X).PreservesInjectiveObjects := sorry

/-- The inverse-image square for a topology comparison, bundled as an isomorphism between
composites of exact functors on abelian sheaves. -/
@[stacks 0EZ3 "exact topology-comparison inverse-image square"]
noncomputable def overMapPullbackComparisonExactIso
    (hle : τ' ≤ τ) {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f]
    [HasSheafify (τ.over X) AddCommGrpCat.{max u v}]
    [HasSheafify (τ.over Y) AddCommGrpCat.{max u v}] :
    (τ'.overMapPullbackExact f).comp (comparisonTopologyPullbackAbExact hle X) ≅
      (comparisonTopologyPullbackAbExact hle Y).comp (τ.overMapPullbackExact f) :=
  (exactFunctor _ _).isoMk
    (overMapPullbackComparisonIso (A := AddCommGrpCat.{max u v}) hle f)

end Abelian

/- The comparison `Iso` has explicit Lan and sheafification components.  Its reported `sorryAx`
comes from inherited Prop-valued continuity and sheafification laws. -/

end CategoryTheory.GrothendieckTopology
