module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import ReasLib.CategoryTheory.Filtration.Complex.StageTower
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Filtered realizations of derived inverse systems

A filtered complex determines an inverse system in the derived category through its
filtration stages, together with a canonical cocone to its underlying complex. This file
packages that construction, its functoriality, and a concrete realization bundle.
-/

open CategoryTheory.Limits Opposite

noncomputable section

universe t w v u

namespace CategoryTheory.FilteredComplex

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{t} A]

/-- The inverse-system tower in the derived category obtained by localizing the integer
filtration-stage tower. -/
@[stacks 0ESJ "derived stage tower"]
noncomputable abbrev derivedTower (K : FilteredComplex A) : ℤᵒᵖ ⥤ DerivedCategory A :=
  StageTower.diagram K ⋙ DerivedCategory.Q

/-- A filtered-complex morphism induces a map between the corresponding derived towers. -/
@[stacks 0ESJ "map of derived stage towers"]
noncomputable abbrev derivedTowerMap {K L : FilteredComplex A} (f : K ⟶ L) :
    K.derivedTower ⟶ L.derivedTower :=
  Functor.whiskerRight (StageTower.map f) DerivedCategory.Q

/-- The derived tower map induced by an identity is the identity. -/
@[simp]
theorem derivedTowerMap_id (K : FilteredComplex A) :
    derivedTowerMap (𝟙 K) = 𝟙 K.derivedTower := sorry

/-- Passage to derived stage towers preserves composition. -/
@[simp]
theorem derivedTowerMap_comp {K L M : FilteredComplex A} (f : K ⟶ L) (g : L ⟶ M) :
    derivedTowerMap (f ≫ g) = derivedTowerMap f ≫ derivedTowerMap g := sorry

/-- Taking the derived integer tower is functorial in the filtered complex. -/
@[stacks 0ESJ "derived stage tower functor"]
noncomputable def derivedTowerFunctor :
    FilteredComplex A ⥤ (ℤᵒᵖ ⥤ DerivedCategory A) where
  obj K := K.derivedTower
  map f := derivedTowerMap f
  map_id K := derivedTowerMap_id K
  map_comp f g := derivedTowerMap_comp f g

/-- The derived tower functor sends `K` to its derived stage tower. -/
@[simp]
theorem derivedTowerFunctor_obj (K : FilteredComplex A) :
    (derivedTowerFunctor (A := A)).obj K = K.derivedTower := sorry

/-- A component of the functorial derived tower map is the localized stage map. -/
@[simp]
theorem derivedTowerFunctor_map_app {K L : FilteredComplex A} (f : K ⟶ L)
    (i : ℤᵒᵖ) :
    ((derivedTowerFunctor (A := A)).map f).app i =
      DerivedCategory.Q.map (K.stageMap f i.unop) := sorry

/-- A component of the direct derived-tower map is the localized stage map. -/
@[simp, stacks 0ESJ "component of a derived stage-tower map"]
theorem derivedTowerMap_app {K L : FilteredComplex A} (f : K ⟶ L)
    (i : ℤᵒᵖ) :
    (derivedTowerMap f).app i = DerivedCategory.Q.map (K.stageMap f i.unop) := sorry

/-- Naturality of the filtration-stage maps into the underlying complex. -/
@[reassoc]
theorem derivedCocone_naturality (K : FilteredComplex A)
    {i j : ℤᵒᵖ} (f : i ⟶ j) :
    (K.derivedTower.map f) ≫ DerivedCategory.Q.map (K.stageInclusion j.unop) =
      DerivedCategory.Q.map (K.stageInclusion i.unop) ≫
        ((Functor.const ℤᵒᵖ).obj (DerivedCategory.Q.obj K.underlying)).map f := sorry

/-- The canonical cocone from the derived stage tower to the underlying complex. -/
@[stacks 0ESJ "derived stage cocone"]
noncomputable def derivedCocone (K : FilteredComplex A) : Cocone K.derivedTower :=
  DerivedCategory.Q.mapCocone (StageTower.cocone K)

/-- The point of the derived stage cocone is the localized underlying complex. -/
@[simp, stacks 0ESJ "point of the derived stage cocone"]
theorem derivedCocone_pt (K : FilteredComplex A) :
    K.derivedCocone.pt = DerivedCategory.Q.obj K.underlying := sorry

/-- The legs of the derived stage cocone are the localized filtration inclusions. -/
@[simp, stacks 0ESJ "legs of the derived stage cocone"]
theorem derivedCocone_ι_app (K : FilteredComplex A) (i : ℤᵒᵖ) :
    K.derivedCocone.ι.app i = DerivedCategory.Q.map (K.stageInclusion i.unop) := sorry

/-- Compatibility of the derived cocones with a filtered-complex morphism. -/
@[reassoc]
theorem derivedCoconeMap_w {K L : FilteredComplex A} (f : K ⟶ L) (i : ℤᵒᵖ) :
    K.derivedCocone.ι.app i ≫ DerivedCategory.Q.map (K.underlyingMap f) =
      (derivedTowerMap f).app i ≫ L.derivedCocone.ι.app i := sorry

/-- A filtered-complex morphism induces the canonical morphism from its derived cocone to
the target derived cocone precomposed along the map of derived towers. -/
@[stacks 0ESJ "map of derived stage cocones"]
noncomputable def derivedCoconeMap {K L : FilteredComplex A} (f : K ⟶ L) :
    K.derivedCocone ⟶
      (Cocone.precompose (derivedTowerMap f)).obj L.derivedCocone where
  hom := DerivedCategory.Q.map (K.underlyingMap f)
  w := derivedCoconeMap_w f

/-- The point map of `derivedCoconeMap f` is the localized underlying cochain map. -/
@[simp]
theorem derivedCoconeMap_hom {K L : FilteredComplex A} (f : K ⟶ L) :
    (derivedCoconeMap f).hom = DerivedCategory.Q.map (K.underlyingMap f) := sorry

/-- A concrete filtered-complex realization of a cocone in the derived category. The two
isomorphisms and their compatibility are stored as projections for downstream use. -/
@[stacks 0ESJ "filtered realization owner"]
structure Realization {system : ℤᵒᵖ ⥤ DerivedCategory A} (c : Cocone system) where
  /-- The filtered cochain complex realizing the system. -/
  complex : FilteredComplex A
  /-- The derived filtration-stage tower is the prescribed inverse system. -/
  towerIso : complex.derivedTower ≅ system
  /-- The underlying cochain complex represents the point of the prescribed cocone. -/
  pointIso : DerivedCategory.Q.obj complex.underlying ≅ c.pt
  /-- The stage and point identifications respect every leg of the prescribed cocone. -/
  fac (i : ℤᵒᵖ) :
    DerivedCategory.Q.map (complex.stageInclusion i.unop) ≫ pointIso.hom =
      towerIso.hom.app i ≫ c.ι.app i

namespace Realization

/-- The derived object represented by the `i`-th filtration stage. -/
noncomputable abbrev stageIso {system : ℤᵒᵖ ⥤ DerivedCategory A}
    {c : Cocone system} (R : Realization c) (i : ℤᵒᵖ) :
    DerivedCategory.Q.obj (R.complex.stage i.unop) ≅ system.obj i :=
  R.towerIso.app i

/-- The cocone isomorphism encoded by the point isomorphism and the compatibility field of a
realization. -/
noncomputable def coconeIso {system : ℤᵒᵖ ⥤ DerivedCategory A}
    {c : Cocone system} (R : Realization c) :
    R.complex.derivedCocone ≅ (Cocone.precompose R.towerIso.hom).obj c :=
  Cocone.ext R.pointIso R.fac

/-- The realization compatibility equation, stated using `stageIso`. -/
@[reassoc]
theorem stageIso_hom_comp_legs {system : ℤᵒᵖ ⥤ DerivedCategory A}
    {c : Cocone system} (R : Realization c) (i : ℤᵒᵖ) :
    DerivedCategory.Q.map (R.complex.stageInclusion i.unop) ≫ R.pointIso.hom =
      (R.stageIso i).hom ≫ c.ι.app i := sorry

/-- Lemma 19.13.12: every inverse system over `ℤᵒᵖ` with a compatible cocone in the
derived category of a Grothendieck abelian category has a filtered-complex realization. -/
@[stacks 0ESJ "existence"]
theorem nonempty [IsGrothendieckAbelian.{w} A]
    {system : ℤᵒᵖ ⥤ DerivedCategory A} (c : Cocone system) :
    Nonempty (Realization c) := sorry

end Realization

end CategoryTheory.FilteredComplex
