/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.Derived
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition

@[expose] public section

/-!
# Closed-support comparison for derived sections

This module constructs the diagram of closed-support cohomology objects and
its canonical map to the cohomology of the derived-sections functor.
-/

open CategoryTheory CategoryTheory.Limits Set TopologicalSpace

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.SupportedOn

variable {A : Type u} [CommRing A]

/-- The category of closed subsets of `Spec(A)` contained in `T`. -/
abbrev ClosedSubsets (T : Set (PrimeSpectrum A)) :=
  ObjectProperty.FullSubcategory
    (fun Z : Closeds (PrimeSpectrum A) => (Z : Set (PrimeSpectrum A)) ⊆ T)

/-- A closed support in `ClosedSubsets T` is contained in `T`. -/
theorem mem_closedSubsets {T : Set (PrimeSpectrum A)} (Z : ClosedSubsets T) :
    (Z.obj : Set (PrimeSpectrum A)) ⊆ T := sorry

/-- Closed subsets contained in a fixed subset form a filtered category under inclusion. -/
instance closedSubsetsIsFiltered (T : Set (PrimeSpectrum A)) : IsFiltered (ClosedSubsets T) :=
  sorry

/-- Containment of supports induces containment of the corresponding module properties. -/
theorem supportedOn_mono {T T' : Set (PrimeSpectrum A)} (h : T ⊆ T') :
    (ModuleCat.supportedOn T : ObjectProperty (ModuleCat.{u} A)) ≤
      ModuleCat.supportedOn T' := sorry

/-- The inclusion between supported-module categories induced by `T ⊆ T'` is exact. -/
theorem changeSupport_exact {T T' : Set (PrimeSpectrum A)} (h : T ⊆ T') :
    exactFunctor (category T) (category T')
      (ObjectProperty.ιOfLE (supportedOn_mono h)) := sorry

/-- The exact inclusion from modules supported on `T` to modules supported on `T'`. -/
noncomputable def changeSupport {T T' : Set (PrimeSpectrum A)} (h : T ⊆ T') :
    category T ⥤ₑ category T' :=
  ⟨ObjectProperty.ιOfLE (supportedOn_mono h), changeSupport_exact h⟩

/-- The underlying functor of `changeSupport` is the full-subcategory inclusion. -/
theorem changeSupport_obj {T T' : Set (PrimeSpectrum A)} (h : T ⊆ T') :
    (changeSupport h).obj = ObjectProperty.ιOfLE (supportedOn_mono h) := sorry

/-- Changing support and then including in ambient modules is canonically the original inclusion. -/
noncomputable def changeSupportCompInclusionIso {T T' : Set (PrimeSpectrum A)}
    (h : T ⊆ T') :
    (changeSupport h).comp (exactInclusion T') ≅ exactInclusion T :=
  ObjectProperty.isoMk (exactFunctor (category T) (ModuleCat.{u} A))
    (ObjectProperty.ιOfLECompιIso (supportedOn_mono h))

/-- The exact-functor comparison is induced by the evident equality of ambient inclusions. -/
theorem changeSupportCompInclusionIso_def {T T' : Set (PrimeSpectrum A)}
    (h : T ⊆ T') :
    changeSupportCompInclusionIso h =
      ObjectProperty.isoMk (exactFunctor (category T) (ModuleCat.{u} A))
        (ObjectProperty.ιOfLECompιIso (supportedOn_mono h)) := sorry

/-- After passage to derived categories, changing support and then forgetting support agrees with
forgetting the original support. -/
noncomputable def changeSupportAmbientIso {T T' : Set (PrimeSpectrum A)} (h : T ⊆ T')
    (K : DerivedCategory (category T)) :
    (derivedInclusion T').obj ((changeSupport h).mapDerivedCategory.obj K) ≅
      (derivedInclusion T).obj K :=
  (ExactFunctor.MapDerivedCategory.compObjIso
      (changeSupport h) (exactInclusion T') K).symm ≪≫
    (ExactFunctor.MapDerivedCategory.mapIso (changeSupportCompInclusionIso h)).app K

/-- The ambient derived-support comparison is the composite of the exact-functor comparisons. -/
theorem changeSupportAmbientIso_def {T T' : Set (PrimeSpectrum A)} (h : T ⊆ T')
    (K : DerivedCategory (category T)) :
    changeSupportAmbientIso h K =
      (ExactFunctor.MapDerivedCategory.compObjIso
        (changeSupport h) (exactInclusion T') K).symm ≪≫
        (ExactFunctor.MapDerivedCategory.mapIso (changeSupportCompInclusionIso h)).app K := sorry

/-- The canonical map between ambient derived sections induced by `T ⊆ T'`. -/
noncomputable def derivedSupportMap {T T' : Set (PrimeSpectrum A)} (h : T ⊆ T')
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (derivedInclusion T).obj ((derivedSections T).obj K) ⟶
      (derivedInclusion T').obj ((derivedSections T').obj K) :=
  let X := (derivedSections T).obj K
  let e := changeSupportAmbientIso h X
  e.inv ≫ (derivedInclusion T').map
    (derivedHomEquiv T' ((changeSupport h).mapDerivedCategory.obj X) K
      (e.hom ≫ (derivedAdjunction T).counit.app K))

/-- The derived support map for a reflexive containment is the identity. -/
theorem derivedSupportMap_id (T : Set (PrimeSpectrum A))
    (K : DerivedCategory (ModuleCat.{u} A)) :
    derivedSupportMap (Subset.rfl : T ⊆ T) K = 𝟙 _ := sorry

/-- Derived support maps compose according to transitivity of support containment. -/
theorem derivedSupportMap_comp {T T' T'' : Set (PrimeSpectrum A)}
    (h : T ⊆ T') (h' : T' ⊆ T'') (K : DerivedCategory (ModuleCat.{u} A)) :
    derivedSupportMap (h.trans h') K =
      derivedSupportMap h K ≫ derivedSupportMap h' K := sorry

/-- Cohomology in degree `i` of the established derived-sections object with support in `T`. -/
noncomputable abbrev cohomology (T : Set (PrimeSpectrum A))
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) : ModuleCat.{u} A :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
    ((derivedInclusion T).obj ((derivedSections T).obj K))

/-- Supported cohomology is homology after `derivedSections`, followed by the supported-category
inclusion. -/
theorem cohomology_def (T : Set (PrimeSpectrum A))
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    cohomology T K i =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        ((derivedInclusion T).obj ((derivedSections T).obj K)) := sorry

/-- The cohomology map associated to an inclusion of two closed supports. -/
noncomputable def closedMap {T : Set (PrimeSpectrum A)}
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) {Z W : ClosedSubsets T} (f : Z ⟶ W) :
    cohomology (Z.obj : Set (PrimeSpectrum A)) K i ⟶
      cohomology (W.obj : Set (PrimeSpectrum A)) K i :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
    (derivedSupportMap (leOfHom f.hom) K)

/-- The closed-support cohomology map preserves identities. -/
theorem closedMap_id {T : Set (PrimeSpectrum A)}
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) (Z : ClosedSubsets T) :
    closedMap K i (𝟙 Z) = 𝟙 _ := sorry

/-- The closed-support cohomology map preserves composition. -/
theorem closedMap_comp {T : Set (PrimeSpectrum A)}
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) {Z W V : ClosedSubsets T}
    (f : Z ⟶ W) (g : W ⟶ V) :
    closedMap K i (f ≫ g) = closedMap K i f ≫ closedMap K i g := sorry

/-- The diagram of cohomology objects indexed by closed subsets of `T`. -/
noncomputable def closedDiagram (T : Set (PrimeSpectrum A))
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) : ClosedSubsets T ⥤ ModuleCat.{u} A where
  obj Z := cohomology (Z.obj : Set (PrimeSpectrum A)) K i
  map f := closedMap K i f
  map_id Z := closedMap_id K i Z
  map_comp f g := closedMap_comp K i f g

/-- The closed-support diagram has the expected value at each closed subset. -/
theorem closedDiagram_obj (T : Set (PrimeSpectrum A))
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) (Z : ClosedSubsets T) :
    (closedDiagram T K i).obj Z = cohomology (Z.obj : Set (PrimeSpectrum A)) K i := sorry

/-- The closed-support diagram acts through the canonical derived support map. -/
theorem closedDiagram_map {T : Set (PrimeSpectrum A)}
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) {Z W : ClosedSubsets T} (f : Z ⟶ W) :
    (closedDiagram T K i).map f = closedMap K i f := sorry

/-- The map from a closed-support cohomology stage to cohomology supported on `T`. -/
noncomputable def stageMap (T : Set (PrimeSpectrum A))
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) (Z : ClosedSubsets T) :
    (closedDiagram T K i).obj Z ⟶ cohomology T K i :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
    (derivedSupportMap Z.property K)

/-- The closed-stage maps form a cocone over the closed-support diagram. -/
theorem stageMap_naturality (T : Set (PrimeSpectrum A))
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ)
    {Z W : ClosedSubsets T} (f : Z ⟶ W) :
    (closedDiagram T K i).map f ≫ stageMap T K i W =
      stageMap T K i Z ≫ 𝟙 (cohomology T K i) := sorry

/-- The canonical cocone from closed-support stages to support on `T`. -/
noncomputable def cocone (T : Set (PrimeSpectrum A))
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) : Cocone (closedDiagram T K i) :=
  Cocone.mk (cohomology T K i)
    { app := stageMap T K i
      naturality := fun {_ _} f ↦ stageMap_naturality T K i f }

/-- A leg of the canonical cocone is the corresponding closed-stage map. -/
theorem cocone_ι_app (T : Set (PrimeSpectrum A))
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) (Z : ClosedSubsets T) :
    (cocone T K i).ι.app Z = stageMap T K i Z := sorry

/-- The canonical map from the colimit of closed-support cohomology to support on `T`. -/
noncomputable def comparison (T : Set (PrimeSpectrum A))
    (hT : StableUnderSpecialization T) (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    colimit (closedDiagram T K i) ⟶ cohomology T K i :=
  colimit.desc (closedDiagram T K i) (cocone T K i)

/-- The comparison map restricts to the canonical map on every closed stage. -/
theorem ι_comp_comparison (T : Set (PrimeSpectrum A))
    (hT : StableUnderSpecialization T) (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ)
    (Z : ClosedSubsets T) :
    colimit.ι (closedDiagram T K i) Z ≫ comparison T hT K i = stageMap T K i Z := sorry

/-- For a Noetherian ring and specialization-stable support, the closed-support comparison is an isomorphism. -/
theorem comparisonIsIso {A : Type u} [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    IsIso (comparison T hT K i) := sorry

end CategoryTheory.ModuleCat.SupportedOn
