module

public import ReasLib.CategoryTheory.Sites.TopologyComparison.Situation
public import ReasLib.CategoryTheory.Sites.Cohomology.Objectwise
public import ReasLib.CategoryTheory.Sites.Sheafification.FreeAbelianYoneda.Pullback
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Cohomology comparisons for an exact inverse image

The generic map is built from the exact-functor action on `Ext`, the canonical pullback of the
free abelian representable, and a coefficient morphism.  The topology-comparison specialization
uses the adjunction counit, so its source is an arbitrary fine-topology sheaf; membership in the
selected coefficient family is used only by the later injectivity theorem.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Sheaf

noncomputable section

universe u v w z

namespace CategoryTheory.Sheaf.Cohomology

variable {C : Type u} [Category.{v} C]

/-- The universe-heterogeneous objectwise cohomology map induced by an exact inverse image.
The representing object is the universe-raised free abelian Yoneda sheaf, so the site universe
and the output universe of `Ext` remain independent. -/
@[stacks 0EZC "universe-heterogeneous exact inverse-image cohomology map"]
noncomputable def mapOfExactPullback
    {J K : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max w v}]
    [HasSheafify K AddCommGrpCat.{max w v}]
    [HasExt.{z} (Sheaf J AddCommGrpCat.{max w v})]
    [HasExt.{z} (Sheaf K AddCommGrpCat.{max w v})]
    (P : Sheaf J AddCommGrpCat.{max w v} ⥤ Sheaf K AddCommGrpCat.{max w v})
    [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (e : GrothendieckTopology.FreeAbelianYoneda.ULift.obj.{w} K U ≅
      P.obj (GrothendieckTopology.FreeAbelianYoneda.ULift.obj.{w} J U))
    {F : Sheaf J AddCommGrpCat.{max w v}}
    (target : Sheaf K AddCommGrpCat.{max w v}) (c : P.obj F ⟶ target) (p : ℕ) :
    (Sheaf.cohomologyOverPresheafFunctor J
      (uliftYoneda.{w}.obj U) p).obj F ⟶
      (Sheaf.cohomologyOverPresheafFunctor K
        (uliftYoneda.{w}.obj U) p).obj target :=
  AddCommGrpCat.ofHom <|
    ((Abelian.Ext.mk₀ c).postcomp
      (GrothendieckTopology.FreeAbelianYoneda.ULift.obj.{w} K U) (add_zero p)).comp
      (((Abelian.Ext.mk₀ e.hom).precomp (P.obj F) (zero_add p)).comp
        (P.mapExtAddHom
          (GrothendieckTopology.FreeAbelianYoneda.ULift.obj.{w} J U) F p))

end CategoryTheory.Sheaf.Cohomology

namespace CategoryTheory.GrothendieckTopology.TopologyComparison.Cohomology

variable {C : Type u} [Category.{v} C]
variable {τ τ' : GrothendieckTopology C}

/-- The universe-heterogeneous free-representable pullback isomorphism for a topology comparison
on a slice. -/
@[stacks 0EZC "universe-heterogeneous topology-comparison representable pullback"]
noncomputable def generatorPullbackIso
    (hle : τ' ≤ τ) (X : C)
    [HasWeakSheafify (τ.over X) AddCommGrpCat.{max u v}]
    [HasWeakSheafify (τ'.over X) AddCommGrpCat.{max u v}] :
    FreeAbelianYoneda.ULift.obj.{u} (τ.over X) (Over.mk (𝟙 X)) ≅
      (comparisonTopologyPullback AddCommGrpCat.{max u v} hle X).obj
        (FreeAbelianYoneda.ULift.obj.{u} (τ'.over X) (Over.mk (𝟙 X))) :=
  -- The identity-slice continuity certificate is indexed by `hle` and is intentionally scoped to
  -- the concrete pullback isomorphism.
  let _ := comparisonOver_id_isContinuous hle X
  FreeAbelianYoneda.ULift.pullbackIso
    (J := τ'.over X) (K := τ.over X) (Over.mk (𝟙 X))

/-- The canonical map from cohomology on the coarser topology to cohomology after exact inverse
image to the finer topology.  It is the exact-pullback Ext map with identity coefficient
morphism; coefficient vanishing is needed only to prove that this map is invertible. -/
@[stacks 0EZH "canonical degreewise topology-comparison map"]
noncomputable def pullbackMap
    (hle : τ' ≤ τ) (X : C)
    [HasSheafify (τ.over X) AddCommGrpCat.{max u v}]
    [HasSheafify (τ'.over X) AddCommGrpCat.{max u v}]
    [HasExt.{z} (Sheaf (τ.over X) AddCommGrpCat.{max u v})]
    [HasExt.{z} (Sheaf (τ'.over X) AddCommGrpCat.{max u v})]
    (F : Sheaf (τ'.over X) AddCommGrpCat.{max u v}) (p : ℕ) :
    Sheaf.cohomologyOverObject F (Over.mk (𝟙 X)) p ⟶
      Sheaf.cohomologyOverObject
        ((comparisonTopologyPullback AddCommGrpCat.{max u v} hle X).obj F)
        (Over.mk (𝟙 X)) p :=
  Sheaf.Cohomology.mapOfExactPullback
    (U := Over.mk (𝟙 X))
    (P := comparisonTopologyPullback AddCommGrpCat.{max u v} hle X)
    (e := generatorPullbackIso hle X)
    ((comparisonTopologyPullback AddCommGrpCat.{max u v} hle X).obj F)
    (𝟙 _) p

/-- The coarse-to-fine topology-comparison map is natural in the coefficient sheaf. -/
@[stacks 0EZH "naturality of the degreewise topology-comparison map"]
theorem pullbackMap_naturality
    (hle : τ' ≤ τ) (X : C)
    [HasSheafify (τ.over X) AddCommGrpCat.{max u v}]
    [HasSheafify (τ'.over X) AddCommGrpCat.{max u v}]
    [HasExt.{max u v} (Sheaf (τ.over X) AddCommGrpCat.{max u v})]
    [HasExt.{max u v} (Sheaf (τ'.over X) AddCommGrpCat.{max u v})]
    {F G : Sheaf (τ'.over X) AddCommGrpCat.{max u v}} (α : F ⟶ G) (p : ℕ) :
    (Sheaf.cohomologyOverObjectFunctor (τ'.over X) (Over.mk (𝟙 X)) p).map α ≫
        pullbackMap hle X G p =
      pullbackMap hle X F p ≫
        (Sheaf.cohomologyOverObjectFunctor (τ.over X) (Over.mk (𝟙 X)) p).map
          ((comparisonTopologyPullback AddCommGrpCat.{max u v} hle X).map α) := sorry

/-- The coarse-to-fine topology-comparison maps assembled as a natural transformation in the
coefficient sheaf.  Its components are `pullbackMap`; only naturality is deferred proof data. -/
@[stacks 0EZH "functorial degreewise topology-comparison map"]
noncomputable def pullbackNatTrans
    (hle : τ' ≤ τ) (X : C)
    [HasSheafify (τ.over X) AddCommGrpCat.{max u v}]
    [HasSheafify (τ'.over X) AddCommGrpCat.{max u v}]
    [HasExt.{max u v} (Sheaf (τ.over X) AddCommGrpCat.{max u v})]
    [HasExt.{max u v} (Sheaf (τ'.over X) AddCommGrpCat.{max u v})]
    (p : ℕ) :
    Sheaf.cohomologyOverObjectFunctor (τ'.over X) (Over.mk (𝟙 X)) p ⟶
      comparisonTopologyPullback AddCommGrpCat.{max u v} hle X ⋙
        Sheaf.cohomologyOverObjectFunctor (τ.over X) (Over.mk (𝟙 X)) p where
  app F := pullbackMap hle X F p
  naturality _ _ α := pullbackMap_naturality hle X α p

/-- The universe-heterogeneous objectwise topology-comparison edge map.  Its source is an
arbitrary `τ`-sheaf and its target is the corresponding `τ'` direct image; coefficient membership
is intentionally left to the injectivity and range theorems below. -/
@[stacks 0EZC "universe-heterogeneous topology-comparison edge map"]
noncomputable def edgeMap
    (hle : τ' ≤ τ) (X : C)
    [HasSheafify (τ.over X) AddCommGrpCat.{max u v}]
    [HasSheafify (τ'.over X) AddCommGrpCat.{max u v}]
    [HasExt.{z} (Sheaf (τ.over X) AddCommGrpCat.{max u v})]
    [HasExt.{z} (Sheaf (τ'.over X) AddCommGrpCat.{max u v})]
    (F : Sheaf (τ.over X) AddCommGrpCat.{max u v}) (p : ℕ) :
    Sheaf.cohomologyOverObject
        ((comparisonTopologyPushforward AddCommGrpCat.{max u v} hle X).obj F)
        (Over.mk (𝟙 X)) p ⟶
      Sheaf.cohomologyOverObject F (Over.mk (𝟙 X)) p :=
  Sheaf.Cohomology.mapOfExactPullback
    (U := Over.mk (𝟙 X))
    (P := comparisonTopologyPullback AddCommGrpCat.{max u v} hle X)
    (e := generatorPullbackIso hle X)
    F
    ((comparisonTopologyAdjunction AddCommGrpCat.{max u v} hle X).counit.app F) p

/-- The topology-comparison edge map is natural in the coefficient sheaf.  This is the
source-facing specification needed to transport classes along a morphism without unfolding the
Ext construction of `edgeMap`. -/
@[stacks 0EZC "edge-map naturality"]
theorem edgeMap_naturality
    (hle : τ' ≤ τ) (X : C)
    [HasSheafify (τ.over X) AddCommGrpCat.{max u v}]
    [HasSheafify (τ'.over X) AddCommGrpCat.{max u v}]
    [HasExt.{max u v} (Sheaf (τ.over X) AddCommGrpCat.{max u v})]
    [HasExt.{max u v} (Sheaf (τ'.over X) AddCommGrpCat.{max u v})]
    {F G : Sheaf (τ.over X) AddCommGrpCat.{max u v}} (α : F ⟶ G) (p : ℕ) :
    (Sheaf.cohomologyOverObjectFunctor (τ'.over X) (Over.mk (𝟙 X)) p).map
          ((comparisonTopologyPushforward AddCommGrpCat.{max u v} hle X).map α) ≫
        edgeMap hle X G p =
      edgeMap hle X F p ≫
        (Sheaf.cohomologyOverObjectFunctor (τ.over X) (Over.mk (𝟙 X)) p).map α := sorry

/-- The topology-comparison edge maps assembled as a natural transformation in the coefficient
sheaf.  Its components are the concrete maps `edgeMap`; only their naturality law is proof data. -/
@[stacks 0EZC "functorial topology-comparison edge map"]
noncomputable def edgeNatTrans
    (hle : τ' ≤ τ) (X : C)
    [HasSheafify (τ.over X) AddCommGrpCat.{max u v}]
    [HasSheafify (τ'.over X) AddCommGrpCat.{max u v}]
    [HasExt.{max u v} (Sheaf (τ.over X) AddCommGrpCat.{max u v})]
    [HasExt.{max u v} (Sheaf (τ'.over X) AddCommGrpCat.{max u v})]
    (p : ℕ) :
    comparisonTopologyPushforward AddCommGrpCat.{max u v} hle X ⋙
        Sheaf.cohomologyOverObjectFunctor (τ'.over X) (Over.mk (𝟙 X)) p ⟶
      Sheaf.cohomologyOverObjectFunctor (τ.over X) (Over.mk (𝟙 X)) p where
  app F := edgeMap hle X F p
  naturality _ _ α := edgeMap_naturality hle X α p

/-- Classes in the target of `edgeMap` that vanish on a covering of the terminal slice
object. -/
@[stacks 0EZC "universe-heterogeneous topology-comparison locally zero class"]
def locallyZero
    (τ' : GrothendieckTopology C) (X : C)
    [HasSheafify (τ.over X) AddCommGrpCat.{max u v}]
    [HasExt.{z} (Sheaf (τ.over X) AddCommGrpCat.{max u v})]
    (F : Sheaf (τ.over X) AddCommGrpCat.{max u v}) (p : ℕ)
    (ξ : Sheaf.cohomologyOverObject F (Over.mk (𝟙 X)) p) : Prop :=
  Presheaf.IsLocallyZero (τ'.over X)
    (Sheaf.uliftCohomologyPresheaf (τ.over X) F p) ξ

/-- Lemma 21.30.5 (0EZC) (1): the universe-heterogeneous edge map is injective on `A_X`. -/
@[stacks 0EZC "(1)"]
theorem edgeMap_injective
    (hle : τ' ≤ τ)
    (P : MorphismProperty C)
    (A' : ∀ X : C,
      ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))
    [∀ X : C, HasSheafify (τ.over X) AddCommGrpCat.{max u v}]
    [∀ X : C, HasSheafify (τ'.over X) AddCommGrpCat.{max u v}]
    [∀ X : C, HasExt.{max u v} (Sheaf (τ.over X) AddCommGrpCat.{max u v})]
    [∀ X : C, HasExt.{max u v} (Sheaf (τ'.over X) AddCommGrpCat.{max u v})]
    (h : Situation τ τ' P A') (n : ℕ) (hVn : h.LocalVanishing n)
    (X : C) (F : Sheaf (τ.over X) AddCommGrpCat.{max u v})
    (hF : TopologyComparison.objectProperty hle A' X F) :
    Function.Injective (edgeMap hle X F (n + 1)) := sorry

/-- Lemma 21.30.5 (0EZC) (2): the range of the universe-heterogeneous edge map is exactly the
classes which are locally zero on the comparison topology. -/
@[stacks 0EZC "(2)"]
theorem mem_range_edgeMap_iff
    (hle : τ' ≤ τ)
    (P : MorphismProperty C)
    (A' : ∀ X : C,
      ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))
    [∀ X : C, HasSheafify (τ.over X) AddCommGrpCat.{max u v}]
    [∀ X : C, HasSheafify (τ'.over X) AddCommGrpCat.{max u v}]
    [∀ X : C, HasExt.{max u v} (Sheaf (τ.over X) AddCommGrpCat.{max u v})]
    [∀ X : C, HasExt.{max u v} (Sheaf (τ'.over X) AddCommGrpCat.{max u v})]
    (h : Situation τ τ' P A') (n : ℕ) (hVn : h.LocalVanishing n)
    (X : C) (F : Sheaf (τ.over X) AddCommGrpCat.{max u v})
    (hF : TopologyComparison.objectProperty hle A' X F)
    (ξ : Sheaf.cohomologyOverObject F (Over.mk (𝟙 X)) (n + 1)) :
    ξ ∈ Set.range (edgeMap hle X F (n + 1)) ↔
      locallyZero τ' X F (n + 1) ξ := sorry

end CategoryTheory.GrothendieckTopology.TopologyComparison.Cohomology
