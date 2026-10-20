/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.HomDiagram
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Composition
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Perfect
public import Mathlib.RingTheory.FinitePresentation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Filtered scalar-extension descent

@stack 0DHX

This leaf records the reusable relative-ring interface behind filtered base-change descent.  The
two ring diagrams, their colimit cocones, the relative maps, and the target compatibility are
explicit data.  The descent assertion is proposition-valued; no stage object or comparison map is
hidden behind an existential choice.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace CategoryTheory.ModuleCat.DerivedExtension

variable {I : Type v} [Category.{w} I]

/-- `0DHX`: a filtered system of relative algebras together with both colimit cocones. -/
@[stacks 0DHX "relative filtered scalar-extension diagram"]
structure RelativeDiagram where
  /-- The filtered diagram of base rings. -/
  base : I ⥤ CommRingCat.{u}
  /-- The filtered diagram of algebras over the base stages. -/
  algebra : I ⥤ CommRingCat.{u}
  /-- The relative ring map at every stage, packaged naturally. -/
  relative : base ⟶ algebra
  /-- The explicit algebra structures used by the relative-perfect predicates. -/
  relativeAlg : ∀ i, Algebra (base.obj i) (algebra.obj i)
  /-- The bundled relative maps agree with the supplied algebra maps. -/
  relative_hom : ∀ i,
    @algebraMap (base.obj i) (algebra.obj i) inferInstance inferInstance (relativeAlg i) =
      (relative.app i).hom
  /-- The colimit cocone for the base diagram. -/
  baseCocone : Cocone base
  /-- The colimit cocone for the algebra diagram. -/
  algebraCocone : Cocone algebra
  /-- The induced map from the base colimit to the algebra colimit. -/
  targetMap : baseCocone.pt ⟶ algebraCocone.pt
  /-- The target algebra structure used by `IsPerfectOver`. -/
  targetAlg : Algebra baseCocone.pt algebraCocone.pt
  /-- The target algebra map agrees with `targetMap`. -/
  target_hom :
    @algebraMap baseCocone.pt algebraCocone.pt inferInstance inferInstance targetAlg =
      targetMap.hom
  /-- Compatibility of every stage relative map with the target relative map. -/
  target_natural : ∀ i,
    baseCocone.ι.app i ≫ targetMap = relative.app i ≫ algebraCocone.ι.app i

/-- `0DHX`: a relative diagram rooted at the source algebra, with every stage and the target
exhibited as its scalar base change.  The arrows are concrete data; `IsPushout` records exactly
the equations `Aᵢ = A₀ ⊗[R₀] Rᵢ` and `A = A₀ ⊗[R₀] R`. -/
@[stacks 0DHX "rooted tensor-stage presentation"]
structure RelativeDiagram.Rooted (D : RelativeDiagram (I := I)) where
  /-- The source stage carrying `R₀ → A₀`. -/
  origin : I
  /-- The designated arrow from the source stage to every stage. -/
  toStage : ∀ i, origin ⟶ i
  /-- The designated arrow at the source stage is the identity. -/
  toStage_origin : toStage origin = 𝟙 origin
  /-- The designated arrows commute with every transition map. -/
  toStage_natural : ∀ ⦃i j⦄ (f : i ⟶ j), toStage i ≫ f = toStage j
  /-- Every stage relative algebra is the pushout of the source relative algebra. -/
  stage_isPushout : ∀ i,
    IsPushout (D.relative.app origin) (D.base.map (toStage i))
      (D.algebra.map (toStage i)) (D.relative.app i)
  /-- The target relative algebra is the pushout of the source relative algebra. -/
  target_isPushout :
    IsPushout (D.relative.app origin) (D.baseCocone.ι.app origin)
      (D.algebraCocone.ι.app origin) D.targetMap

namespace RelativeDiagram

variable (D : RelativeDiagram.{u, v, w} (I := I))

/-- The stage algebra at `i`. -/
@[stacks 0DHX "stage algebra in a filtered scalar-extension diagram"]
abbrev stage (i : I) : CommRingCat.{u} := D.algebra.obj i

/-- The target algebra of the relative system. -/
@[stacks 0DHX "target algebra in a filtered scalar-extension diagram"]
abbrev target : CommRingCat.{u} := D.algebraCocone.pt

/-- The derived extension from a stage algebra to the target algebra. -/
@[stacks 0DHX "derived extension from a stage to the target"]
noncomputable abbrev extend (i : I) :
    DerivedCategory (ModuleCat.{u, u} (D.algebra.obj i)) ⥤
      DerivedCategory (ModuleCat.{u, u} D.algebraCocone.pt) :=
  ModuleCat.derivedExtensionOfScalars.{u, u, u} (D.algebraCocone.ι.app i).hom

/-- The source-facing object descent statement for a relative perfect target.
The index category is nonempty because the conclusion selects a stage; in the
rooted source presentation, the origin supplies this premise. -/
@[stacks 0DHX "relative-perfect object descent along a filtered system"]
theorem exists_stage_of_isPerfectOver
    [IsFilteredOrEmpty I] [Nonempty I]
    (hbase : IsColimit D.baseCocone)
    (halgebra : IsColimit D.algebraCocone)
    (hflat : ∀ i,
      @Module.Flat (D.base.obj i) (D.algebra.obj i)
        inferInstance inferInstance (D.relativeAlg i).toModule)
    (hfp : ∀ i,
      @Algebra.FinitePresentation (D.base.obj i) (D.algebra.obj i)
        inferInstance inferInstance (D.relativeAlg i))
    {K : DerivedCategory (ModuleCat D.algebraCocone.pt)}
    (hK : @DerivedCategory.IsPerfectOver D.baseCocone.pt inferInstance
      D.algebraCocone.pt inferInstance D.targetAlg K) :
    ∃ (i : I) (Ki : DerivedCategory (ModuleCat (D.algebra.obj i))),
      @DerivedCategory.IsPerfectOver (D.base.obj i) inferInstance
        (D.algebra.obj i) inferInstance (D.relativeAlg i) Ki ∧
        IsIsomorphic K ((extend D i).obj Ki) := sorry
/- Proof strategy: express relative perfectness as pseudo-coherence plus finite Tor dimension, descend
a finite-presentation model of `K` and its finitely many differentials to a common filtered stage,
and use `hbase`, `halgebra`, `hflat`, and `hfp` to identify its scalar extension with `K` while
preserving both properties. -/

namespace Rooted

variable {D : RelativeDiagram.{u, v, w} (I := I)} (S : D.Rooted)

/-- Universe-aligned derived category for modules over rings in the ring universe. -/
@[stacks 0DHX "universe-aligned derived module category"]
abbrev DMod (A : Type u) [CommRing A] :=
  DerivedCategory (ModuleCat.{u, u} A)

/-- The derived category of the source algebra `A₀`. -/
@[stacks 0DHX "source derived module category"]
abbrev source (S : D.Rooted) :=
  DMod (D.algebra.obj S.origin)

/-- Derived scalar extension from the source algebra to stage `i`. -/
@[stacks 0DHX "derived source-to-stage extension"]
noncomputable abbrev stageExtension (i : I) :
    source S ⥤ DMod (D.algebra.obj i) :=
  ModuleCat.derivedExtensionOfScalars (D.algebra.map (S.toStage i)).hom

/-- Derived scalar extension along a transition in the algebra diagram. -/
@[stacks 0DHX "derived transition extension"]
noncomputable abbrev transitionExtension ⦃i j : I⦄ (f : i ⟶ j) :
    DMod (D.algebra.obj i) ⥤ DMod (D.algebra.obj j) :=
  ModuleCat.derivedExtensionOfScalars (D.algebra.map f).hom

/-- The direct source-to-stage algebra map is the composite through any earlier stage. -/
@[stacks 0DHX "source-to-stage algebra-map composition"]
theorem toStage_hom_comp ⦃i j : I⦄ (f : i ⟶ j) :
    (D.algebra.map f).hom.comp (D.algebra.map (S.toStage i)).hom =
      (D.algebra.map (S.toStage j)).hom := sorry
/- Proof strategy: apply `congrArg CommRingCat.Hom.hom` to `D.algebra.map_comp` and rewrite the
indexing equality with `S.toStage_natural f`. -/

/-- Canonical comparison between iterated and direct extension from `A₀` to a stage. -/
@[stacks 0DHX "source-to-stage derived-extension comparison"]
noncomputable abbrev stageExtensionCompIso ⦃i j : I⦄ (f : i ⟶ j) :
    S.stageExtension i ⋙ transitionExtension (D := D) f ≅ S.stageExtension j :=
  ModuleCat.derivedExtensionOfScalarsCompIso
    (D.algebra.map (S.toStage i)).hom (D.algebra.map f).hom
    (D.algebra.map (S.toStage j)).hom (S.toStage_hom_comp f)

/-- The stage Hom type obtained by extending two fixed source objects to `i`. -/
@[stacks 0DHX "stage Hom type after scalar extension"]
noncomputable abbrev stageHom (K₀ L₀ : source S) (i : I) : Type _ :=
  (S.stageExtension i).obj K₀ ⟶ (S.stageExtension i).obj L₀

/-- The transition map on stage Hom types, transported through the canonical composition
isomorphisms. -/
@[stacks 0DHX "transition map on scalar-extended Homs"]
noncomputable def stageHomMap (K₀ L₀ : source S) ⦃i j : I⦄ (f : i ⟶ j) :
    S.stageHom K₀ L₀ i → S.stageHom K₀ L₀ j :=
  fun β ↦
    (S.stageExtensionCompIso f).inv.app K₀ ≫
      (transitionExtension (D := D) f).map β ≫
        (S.stageExtensionCompIso f).hom.app L₀

/-- The stage Hom transition attached to an identity is the identity function. -/
@[stacks 0DHX "identity law for stage Hom transition"]
theorem stageHomMap_id (K₀ L₀ : source S) (i : I) :
    S.stageHomMap K₀ L₀ (𝟙 i) = 𝟙 (S.stageHom K₀ L₀ i) := sorry
/- Proof strategy: unfold `stageHomMap`, simplify functoriality at `𝟙 i`, and use the identity
coherence of `derivedExtensionOfScalarsCompIso` together with `S.toStage_origin` and
`S.toStage_natural`. -/

/-- Stage Hom transition maps respect composition. -/
@[stacks 0DHX "composition law for stage Hom transition"]
theorem stageHomMap_comp (K₀ L₀ : source S) ⦃i j k : I⦄
    (f : i ⟶ j) (g : j ⟶ k) :
    S.stageHomMap K₀ L₀ (f ≫ g) =
      Function.comp (S.stageHomMap K₀ L₀ g) (S.stageHomMap K₀ L₀ f) := sorry
/- Proof strategy: unfold both stage maps, rewrite `transitionExtension.map_comp`, and use the
associativity coherence of `derivedExtensionOfScalarsCompIso` for the three source-to-stage ring
maps; finish by categorical associativity. -/

/-- The identity law transported to the categorical `Type` morphism wrapper. -/
@[stacks 0DHX "categorical identity law for stage Hom transition"]
theorem stageHomMap_id_cat (K₀ L₀ : source S) (i : I) :
    TypeCat.ofHom (S.stageHomMap K₀ L₀ (𝟙 i)) = 𝟙 _ := sorry
/- Proof strategy: rewrite with `S.stageHomMap_id K₀ L₀ i`; `TypeCat.ofHom` sends the identity
function to the categorical identity. -/

/-- The composition law transported to the categorical `Type` morphism wrapper. -/
@[stacks 0DHX "categorical composition law for stage Hom transition"]
theorem stageHomMap_comp_cat (K₀ L₀ : source S) ⦃i j k : I⦄
    (f : i ⟶ j) (g : j ⟶ k) :
    TypeCat.ofHom (S.stageHomMap K₀ L₀ (f ≫ g)) =
      TypeCat.ofHom (Function.comp (S.stageHomMap K₀ L₀ g) (S.stageHomMap K₀ L₀ f)) := sorry
/- Proof strategy: apply `congrArg TypeCat.ofHom` to
`S.stageHomMap_comp K₀ L₀ f g`. -/

/-- The concrete functor of stage Hom types. -/
@[stacks 0DHX "functor of scalar-extended stage Homs"]
noncomputable def stageHomFunctor (K₀ L₀ : source S) : I ⥤ Type _ where
  obj i := S.stageHom K₀ L₀ i
  map f := TypeCat.ofHom (S.stageHomMap K₀ L₀ f)
  map_id i := S.stageHomMap_id_cat K₀ L₀ i
  map_comp f g := S.stageHomMap_comp_cat K₀ L₀ f g

/-- Derived scalar extension from the source algebra directly to the target algebra. -/
@[stacks 0DHX "derived source-to-target extension"]
noncomputable abbrev targetExtension :
    source S ⥤ DMod D.algebraCocone.pt :=
  ModuleCat.derivedExtensionOfScalars (D.algebraCocone.ι.app S.origin).hom

/- The unrooted theorem above is useful when stagewise flatness and finite presentation are
  already packaged by a caller.  The textbook setup only assumes these properties at the root;
  the pushout fields of `S` are the intended transport boundary. -/
/-- Lemma 15.85.7 (1), Stacks `0DHX`: for a filtered tensor-stage system, flatness and finite
presentation of the origin algebra suffice for descent of a target-perfect object to a perfect
stage. -/
@[stacks 0DHX "rooted relative-perfect object descent"]
theorem exists_stage_of_isPerfectOver
    [IsFilteredOrEmpty I]
    (hbase : IsColimit D.baseCocone)
    (halgebra : IsColimit D.algebraCocone)
    (hflat : @Module.Flat (D.base.obj S.origin) (D.algebra.obj S.origin)
      inferInstance inferInstance (D.relativeAlg S.origin).toModule)
    (hfp : @Algebra.FinitePresentation (D.base.obj S.origin) (D.algebra.obj S.origin)
      inferInstance inferInstance (D.relativeAlg S.origin))
    {K : DMod D.algebraCocone.pt}
    (hK : @DerivedCategory.IsPerfectOver D.baseCocone.pt inferInstance
      D.algebraCocone.pt inferInstance D.targetAlg K) :
    ∃ (i : I) (Ki : DMod (D.algebra.obj i)),
      @DerivedCategory.IsPerfectOver (D.base.obj i) inferInstance
        (D.algebra.obj i) inferInstance (D.relativeAlg i) Ki ∧
        IsIsomorphic K ((D.extend i).obj Ki) := sorry
/- Proof strategy: use each `S.stage_isPushout i` to transport root flatness and finite
presentation to the stage relative map, use `S.target_isPushout` for the target comparison, and
apply `RelativeDiagram.exists_stage_of_isPerfectOver D hbase halgebra` with those stagewise
hypotheses. -/

/-- The source-to-target algebra map factors through every stage. -/
@[stacks 0DHX "source-to-target algebra-map factorization"]
theorem toTarget_hom_comp (i : I) :
    (D.algebraCocone.ι.app i).hom.comp (D.algebra.map (S.toStage i)).hom =
      (D.algebraCocone.ι.app S.origin).hom := sorry
/- Proof strategy: take the underlying ring-hom equality in naturality of the colimit cocone
`D.algebraCocone.ι` at `S.toStage i`, then simplify the cocone composition. -/

/-- Canonical comparison between extension through stage `i` and direct target extension. -/
@[stacks 0DHX "stage-to-target derived-extension comparison"]
noncomputable abbrev targetExtensionCompIso (i : I) :
    S.stageExtension i ⋙ D.extend i ≅ S.targetExtension :=
  ModuleCat.derivedExtensionOfScalarsCompIso
    (D.algebra.map (S.toStage i)).hom (D.algebraCocone.ι.app i).hom
    (D.algebraCocone.ι.app S.origin).hom (S.toTarget_hom_comp i)

/-- The target Hom type after direct derived scalar extension from `A₀` to `A`. -/
@[stacks 0DHX "target Hom type for the scalar-extension system"]
noncomputable abbrev targetHom (K₀ L₀ : source S) : Type _ :=
  (S.targetExtension).obj K₀ ⟶ (S.targetExtension).obj L₀

/-- The canonical map from a stage Hom type to the target Hom type. -/
@[stacks 0DHX "map from a scalar-extended stage Hom to the target Hom"]
noncomputable def stageToTargetHom (K₀ L₀ : source S) (i : I) :
    S.stageHom K₀ L₀ i → S.targetHom K₀ L₀ :=
  fun β ↦
    (S.targetExtensionCompIso i).inv.app K₀ ≫ (D.extend i).map β ≫
      (S.targetExtensionCompIso i).hom.app L₀

/-- The stage-to-target Hom maps commute with every transition. -/
@[stacks 0DHX "naturality of stage-to-target Hom maps"]
theorem stageToTargetHom_natural (K₀ L₀ : source S) ⦃i j : I⦄
    (f : i ⟶ j) (β : S.stageHom K₀ L₀ i) :
    S.stageToTargetHom K₀ L₀ j (S.stageHomMap K₀ L₀ f β) =
      S.stageToTargetHom K₀ L₀ i β := sorry
/- Proof strategy: unfold `stageToTargetHom` and `stageHomMap`, use functoriality of `D.extend`,
and apply the compatibility between `stageExtensionCompIso` and `targetExtensionCompIso` induced
by `toTarget_hom_comp`; reassociate the resulting composites. -/

/-- The naturality proof in the exact binder shape required by `HomDiagram`. -/
@[stacks 0DHX "naturality witness for the canonical Hom diagram"]
theorem homDiagram_natural (K₀ L₀ : source S) :
    ∀ ⦃i j : I⦄ (f : i ⟶ j) (β : S.stageHom K₀ L₀ i),
      S.stageToTargetHom K₀ L₀ j (S.stageHomMap K₀ L₀ f β) =
        S.stageToTargetHom K₀ L₀ i β := sorry
/- Proof strategy: introduce `i`, `j`, `f`, and `β`, then apply
`S.stageToTargetHom_natural K₀ L₀ f β`. -/

/-- Naturality after the stage maps are bundled as morphisms in `Type`. -/
@[stacks 0DHX "bundled naturality witness for the canonical Hom diagram"]
theorem homDiagram_natural_cat (K₀ L₀ : source S) :
    ∀ ⦃i j : I⦄ (f : i ⟶ j) (β : (S.stageHomFunctor K₀ L₀).obj i),
      S.stageToTargetHom K₀ L₀ j ((S.stageHomFunctor K₀ L₀).map f β) =
        S.stageToTargetHom K₀ L₀ i β := sorry
/- Proof strategy: unfold the map field of `stageHomFunctor` and reduce to
`S.homDiagram_natural K₀ L₀ f β`. -/

/-- The canonical Hom diagram for the rooted tensor-stage presentation. -/
@[stacks 0DHX "canonical Hom diagram for a rooted tensor-stage system"]
noncomputable def homDiagram (K₀ L₀ : source S) :
    DerivedCategory.FilteredColimit.HomDiagram
      (S.stageHomFunctor K₀ L₀) (S.targetHom K₀ L₀) :=
  { ι := S.stageToTargetHom K₀ L₀
    natural := S.homDiagram_natural_cat K₀ L₀ }

/-- The proposition that the canonical Hom cocone is a colimit.  `IsColimit` is a universal
property structure in `Type`, so this wrapper keeps the source-facing assertion proposition-valued
without exposing a chosen universal-property witness as data. -/
@[stacks 0DHX "proposition-valued Hom colimit condition"]
abbrev HomColimit (K₀ L₀ : source S) : Prop :=
  Nonempty (IsColimit (S.homDiagram K₀ L₀).cocone)

/-- Lemma 15.85.7 (2), Stacks `0DHX`: for a flat finitely presented source algebra, a
pseudo-coherent source and a target of finite Tor dimension over the source base ring, the
canonical stage Hom cocone is a filtered colimit.  Unlike the generic `HomDiagram.comparison`,
this proposition does not ask the caller to supply the desired Hom-colimit property. -/
@[stacks 0DHX "canonical filtered colimit of scalar-extended Homs"]
theorem homDiagram_isColimit_exists
    [IsFilteredOrEmpty I]
    (hbase : IsColimit D.baseCocone)
    (halgebra : IsColimit D.algebraCocone)
    (hflat : @Module.Flat (D.base.obj S.origin) (D.algebra.obj S.origin)
      inferInstance inferInstance (D.relativeAlg S.origin).toModule)
    (hfp : @Algebra.FinitePresentation (D.base.obj S.origin) (D.algebra.obj S.origin)
      inferInstance inferInstance (D.relativeAlg S.origin))
    (K₀ L₀ : source S) (hK₀ : K₀.IsPseudoCoherent)
    (hL₀ : @DerivedCategory.HasFiniteTorDimensionOver
      (D.base.obj S.origin) inferInstance (D.algebra.obj S.origin) inferInstance
        (D.relativeAlg S.origin) L₀) :
    S.HomColimit K₀ L₀ := sorry
/- Proof strategy: model `K₀` by a bounded-above finite-presentation complex and `L₀` by a bounded
relative-flat complex, descend the finitely many maps and homotopies through the filtered rooted
system, and apply the generic `DerivedCategory.FilteredColimit.HomDiagram` colimit criterion to the
explicit `S.homDiagram K₀ L₀`. -/

/-- `0DHX` (Hom factorization): every target morphism is represented by one canonical stage map
under the source flatness, finite-presentation, pseudo-coherence, and finite-Tor hypotheses. -/
@[stacks 0DHX "source-faithful Hom factorization"]
theorem hom_factor
    [IsFilteredOrEmpty I]
    (hbase : IsColimit D.baseCocone)
    (halgebra : IsColimit D.algebraCocone)
    (hflat : @Module.Flat (D.base.obj S.origin) (D.algebra.obj S.origin)
      inferInstance inferInstance (D.relativeAlg S.origin).toModule)
    (hfp : @Algebra.FinitePresentation (D.base.obj S.origin) (D.algebra.obj S.origin)
      inferInstance inferInstance (D.relativeAlg S.origin))
    (K₀ L₀ : source S) (hK₀ : K₀.IsPseudoCoherent)
    (hL₀ : @DerivedCategory.HasFiniteTorDimensionOver
      (D.base.obj S.origin) inferInstance (D.algebra.obj S.origin) inferInstance
        (D.relativeAlg S.origin) L₀) :
    ∀ α : S.targetHom K₀ L₀,
      ∃ (i : I) (β : S.stageHom K₀ L₀ i),
        α = S.stageToTargetHom K₀ L₀ i β := sorry
/- Proof strategy: obtain `S.HomColimit K₀ L₀` from `homDiagram_isColimit_exists`, eliminate its
`Nonempty` witness propositionally, and apply the generic `HomDiagram.factor` theorem to `α`. -/

/-- `0DHX` (eventual equality): equality of two stage representatives is witnessed after a later
stage in the rooted filtered system, under the same source hypotheses as `hom_factor`. -/
@[stacks 0DHX "source-faithful eventual equality of Homs"]
theorem hom_eventually_eq
    [IsFilteredOrEmpty I]
    (hbase : IsColimit D.baseCocone)
    (halgebra : IsColimit D.algebraCocone)
    (hflat : @Module.Flat (D.base.obj S.origin) (D.algebra.obj S.origin)
      inferInstance inferInstance (D.relativeAlg S.origin).toModule)
    (hfp : @Algebra.FinitePresentation (D.base.obj S.origin) (D.algebra.obj S.origin)
      inferInstance inferInstance (D.relativeAlg S.origin))
    (K₀ L₀ : source S) (hK₀ : K₀.IsPseudoCoherent)
    (hL₀ : @DerivedCategory.HasFiniteTorDimensionOver
      (D.base.obj S.origin) inferInstance (D.algebra.obj S.origin) inferInstance
        (D.relativeAlg S.origin) L₀)
    (i : I) (x y : S.stageHom K₀ L₀ i)
    (hxy : S.stageToTargetHom K₀ L₀ i x = S.stageToTargetHom K₀ L₀ i y) :
    ∃ (j : I) (f : i ⟶ j),
      S.stageHomMap K₀ L₀ f x = S.stageHomMap K₀ L₀ f y := sorry
/- Proof strategy: obtain the same canonical Hom-colimit witness as in `hom_factor` and apply
`HomDiagram.eventually_eq` to `x`, `y`, and `hxy`. -/

/-- The operational category-colimit property for relative-perfect complexes: every
relative-perfect target object descends to a relative-perfect stage object, and the canonical
Hom diagram is a filtered colimit for the pseudo-coherent/finite-Tor pairs occurring in the
source.  This proposition records the object and morphism clauses without choosing a category
colimit object. -/
@[stacks 0DHX "relative-perfect category-colimit property"]
def IsRelativePerfectCategoryColimit : Prop :=
  (∀ (K : DMod D.algebraCocone.pt),
    @DerivedCategory.IsPerfectOver D.baseCocone.pt inferInstance
        D.algebraCocone.pt inferInstance D.targetAlg K →
      ∃ (i : I) (Ki : DMod (D.algebra.obj i)),
        @DerivedCategory.IsPerfectOver (D.base.obj i) inferInstance
            (D.algebra.obj i) inferInstance (D.relativeAlg i) Ki ∧
          IsIsomorphic K ((D.extend i).obj Ki)) ∧
    ∀ (K₀ L₀ : source S), K₀.IsPseudoCoherent →
      @DerivedCategory.HasFiniteTorDimensionOver
          (D.base.obj S.origin) inferInstance (D.algebra.obj S.origin) inferInstance
            (D.relativeAlg S.origin) L₀ →
        S.HomColimit K₀ L₀

namespace IsRelativePerfectCategoryColimit

/-- The object-descent and Hom-colimit clauses of the relative-perfect category-colimit
property. -/
@[stacks 0DHX "relative-perfect category-colimit specification"]
theorem spec :
    S.IsRelativePerfectCategoryColimit ↔
      ((∀ (K : DMod D.algebraCocone.pt),
        @DerivedCategory.IsPerfectOver D.baseCocone.pt inferInstance
            D.algebraCocone.pt inferInstance D.targetAlg K →
          ∃ (i : I) (Ki : DMod (D.algebra.obj i)),
            @DerivedCategory.IsPerfectOver (D.base.obj i) inferInstance
                (D.algebra.obj i) inferInstance (D.relativeAlg i) Ki ∧
              IsIsomorphic K ((D.extend i).obj Ki)) ∧
        ∀ (K₀ L₀ : source S), K₀.IsPseudoCoherent →
          @DerivedCategory.HasFiniteTorDimensionOver
              (D.base.obj S.origin) inferInstance (D.algebra.obj S.origin) inferInstance
                (D.relativeAlg S.origin) L₀ →
            S.HomColimit K₀ L₀) := sorry
/- Proof strategy: unfold `IsRelativePerfectCategoryColimit`; the right-hand side is its defining
conjunction. -/

end IsRelativePerfectCategoryColimit

/-- Lemma 15.85.7, Stacks `0DHX` (category-colimit consequence): the relative-perfect target
category is the filtered colimit of the relative-perfect stage categories, expressed by its
object-descent and Hom-colimit criterion. -/
@[stacks 0DHX "relative-perfect category colimit"]
theorem isRelativePerfectCategoryColimit
    [IsFilteredOrEmpty I]
    (hbase : IsColimit D.baseCocone)
    (halgebra : IsColimit D.algebraCocone)
    (hflat : @Module.Flat (D.base.obj S.origin) (D.algebra.obj S.origin)
      inferInstance inferInstance (D.relativeAlg S.origin).toModule)
    (hfp : @Algebra.FinitePresentation (D.base.obj S.origin) (D.algebra.obj S.origin)
      inferInstance inferInstance (D.relativeAlg S.origin)) :
    S.IsRelativePerfectCategoryColimit := sorry
/- Proof strategy: use `IsRelativePerfectCategoryColimit.spec`; prove object descent with
`S.exists_stage_of_isPerfectOver hbase halgebra hflat hfp`, and prove the Hom clause with
`S.homDiagram_isColimit_exists hbase halgebra hflat hfp`. -/

end Rooted

end RelativeDiagram

end CategoryTheory.ModuleCat.DerivedExtension
