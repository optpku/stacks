module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Homology.PageTower
public import ReasLib.CategoryTheory.Homology.SpectralSequence.PageShift
public import ReasLib.CategoryTheory.Homology.ShiftedDifferentialObject

/-!
# Spectral Sequences with Page-Dependent Shifts

This module models a spectral sequence whose differential on page `r` has target `T r`, where
`T r` is an autoequivalence of the ambient abelian category.  Each such sequence supplies a
`HomologyPageTower`; consequently its cycle, boundary, quotient, and infinity-page API is shared
with ordinary spectral sequences.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Remark 12.20.3 (Variant) (tag `0AMI`): a shifted spectral sequence with page-dependent
autoequivalences `T r`. Its `r`-th page is a shifted differential object for `T r`, and the
homology of that page is identified with the underlying object of page `r + 1`. -/
@[stacks 0AMI]
structure ShiftedSpectralSequence (T : ℕ+ → (A ≌ A)) where
  /-- The shifted differential object on page `r`. -/
  page (r : ℕ+) : ShiftedDifferentialObject (T r).functor
  /-- The canonical identification of page-`r` homology with the next page object. -/
  iso (r : ℕ+) : (page r).homology ≅ (page (r + 1)).obj

namespace ShiftedSpectralSequence

variable {T : ℕ+ → (A ≌ A)}

/-! ## Morphisms and page functors -/

/-- A morphism of shifted spectral sequences is a pagewise morphism commuting with the
specified homology identifications. -/
@[ext, stacks 0AMI "shifted spectral-sequence morphism"]
structure Hom (S S' : ShiftedSpectralSequence T) where
  /-- The morphism on page `r`. -/
  app (r : ℕ+) : S.page r ⟶ S'.page r
  /-- Compatibility of the pagewise maps with passage to homology. -/
  comm (r : ℕ+) :
    ShiftedDifferentialObject.homologyMap (app r) ≫ (S'.iso r).hom =
      (S.iso r).hom ≫ (app (r + 1)).hom

namespace Hom

/-- The identity page maps commute with the homology identifications. -/
theorem id_comm (S : ShiftedSpectralSequence T) (r : ℕ+) :
    ShiftedDifferentialObject.homologyMap (𝟙 (S.page r)) ≫ (S.iso r).hom =
      (S.iso r).hom ≫ 𝟙 (S.page (r + 1)).obj := sorry

/-- The identity morphism of a shifted spectral sequence. -/
def id (S : ShiftedSpectralSequence T) : Hom S S where
  app r := 𝟙 (S.page r)
  comm r := id_comm S r

/-- Composite page maps commute with the homology identifications. -/
theorem comp_comm {S₁ S₂ S₃ : ShiftedSpectralSequence T}
    (f : Hom S₁ S₂) (g : Hom S₂ S₃) (r : ℕ+) :
    ShiftedDifferentialObject.homologyMap (f.app r ≫ g.app r) ≫ (S₃.iso r).hom =
      (S₁.iso r).hom ≫ (f.app (r + 1) ≫ g.app (r + 1)).hom := sorry

/-- The composite of two morphisms of shifted spectral sequences. -/
def comp {S₁ S₂ S₃ : ShiftedSpectralSequence T} (f : Hom S₁ S₂) (g : Hom S₂ S₃) :
    Hom S₁ S₃ where
  app r := f.app r ≫ g.app r
  comm r := comp_comm f g r

/-- Left identity for shifted-spectral-sequence morphisms. -/
theorem id_comp {S S' : ShiftedSpectralSequence T} (f : Hom S S') :
    comp (id S) f = f := sorry

/-- Right identity for shifted-spectral-sequence morphisms. -/
theorem comp_id {S S' : ShiftedSpectralSequence T} (f : Hom S S') :
    comp f (id S') = f := sorry

/-- Associativity of shifted-spectral-sequence morphism composition. -/
theorem assoc {S₁ S₂ S₃ S₄ : ShiftedSpectralSequence T}
    (f : Hom S₁ S₂) (g : Hom S₂ S₃) (h : Hom S₃ S₄) :
    comp (comp f g) h = comp f (comp g h) := sorry

end Hom

/-- Shifted spectral sequences for a fixed page-dependent shift family form a category. -/
instance : Category (ShiftedSpectralSequence T) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

/-- Evaluation of an identity shifted-spectral-sequence morphism at a page. -/
@[simp]
theorem id_app (S : ShiftedSpectralSequence T) (r : ℕ+) :
    (𝟙 S : S ⟶ S).app r = 𝟙 (S.page r) := sorry

/-- Evaluation of a composite shifted-spectral-sequence morphism at a page. -/
@[simp]
theorem comp_app {S₁ S₂ S₃ : ShiftedSpectralSequence T}
    (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃) (r : ℕ+) :
    (f ≫ g).app r = f.app r ≫ g.app r := sorry

/-- Evaluation at page `r` as a functor to shifted differential objects. -/
@[stacks 0AMI "shifted page evaluation functor"]
def pageFunctor (T : ℕ+ → (A ≌ A)) (r : ℕ+) :
    ShiftedSpectralSequence T ⥤ ShiftedDifferentialObject (T r).functor where
  obj S := S.page r
  map f := f.app r
  map_id S := id_app S r
  map_comp f g := comp_app f g r

namespace PageFunctor

/-- Evaluation of the shifted page functor on an object is its page object. -/
@[simp]
theorem obj (T : ℕ+ → (A ≌ A)) (r : ℕ+)
    (S : ShiftedSpectralSequence T) :
    (pageFunctor T r).obj S = S.page r := sorry

/-- Evaluation of the shifted page functor on a morphism is its page component. -/
@[simp]
theorem map (T : ℕ+ → (A ≌ A)) (r : ℕ+)
    {S S' : ShiftedSpectralSequence T} (f : S ⟶ S') :
    (pageFunctor T r).map f = f.app r := sorry

end PageFunctor

/-- Naturality of the page homology comparison. -/
theorem iso_naturality {S S' : ShiftedSpectralSequence T} (f : S ⟶ S') (r : ℕ+) :
    ShiftedDifferentialObject.homologyMap (f.app r) ≫ (S'.iso r).hom =
      (S.iso r).hom ≫ (f.app (r + 1)).hom := sorry

namespace Page

/-- The natural isomorphism from page-`r` homology to the underlying object of page `r + 1`. -/
@[stacks 0AMI "shifted page homology comparison"]
noncomputable def homologyIso (T : ℕ+ → (A ≌ A)) (r : ℕ+) :
    pageFunctor T r ⋙ ShiftedDifferentialObject.homologyFunctor ≅
      pageFunctor T (r + 1) ⋙ ShiftedDifferentialObject.objFunctor :=
  NatIso.ofComponents (fun S ↦ S.iso r) (fun f ↦ iso_naturality f r)

/-- The forward component of the shifted page-homology comparison is the specified page
comparison. -/
@[simp, stacks 0AMI "shifted page homology comparison component"]
theorem homologyIso_hom_app (T : ℕ+ → (A ≌ A)) (r : ℕ+)
    (S : ShiftedSpectralSequence T) :
    (homologyIso T r).hom.app S = (S.iso r).hom := sorry

/-- The inverse component of the shifted page-homology comparison is the inverse specified page
comparison. -/
@[simp, stacks 0AMI "shifted page homology comparison inverse component"]
theorem homologyIso_inv_app (T : ℕ+ → (A ≌ A)) (r : ℕ+)
    (S : ShiftedSpectralSequence T) :
    (homologyIso T r).inv.app S = (S.iso r).inv := sorry

/-- Evaluation of a shifted spectral sequence at the underlying object of a fixed page. -/
@[stacks 0AMI "shifted page-object functor"]
noncomputable def objFunctor (T : ℕ+ → (A ≌ A)) (r : ℕ+) :
    ShiftedSpectralSequence T ⥤ A :=
  pageFunctor T r ⋙ ShiftedDifferentialObject.objFunctor

namespace ObjFunctor

/-- Evaluation of the shifted page-object functor on a shifted spectral sequence is the
underlying object of the corresponding page. -/
@[simp]
theorem obj (T : ℕ+ → (A ≌ A)) (r : ℕ+)
    (S : ShiftedSpectralSequence T) :
    (objFunctor T r).obj S = (S.page r).obj := sorry

/-- Evaluation of the shifted page-object functor on a morphism is its underlying page map. -/
@[simp]
theorem map (T : ℕ+ → (A ≌ A)) (r : ℕ+)
    {S S' : ShiftedSpectralSequence T} (f : S ⟶ S') :
    (objFunctor T r).map f = (f.app r).hom := sorry

end ObjFunctor

end Page

/-! ## The underlying homology page tower -/

namespace Page

/-- The cycles subobject on shifted page `r`. -/
@[stacks 0AMI "shifted page cycles"]
abbrev cycles (S : ShiftedSpectralSequence T) (r : ℕ+) :
    Subobject (S.page r).obj :=
  kernelSubobject (S.page r).d

/-- The boundaries subobject on shifted page `r`. -/
@[stacks 0AMI "shifted page boundaries"]
abbrev boundaries (S : ShiftedSpectralSequence T) (r : ℕ+) :
    Subobject (S.page r).obj :=
  imageSubobject
    (ShiftedDifferentialObject.Differential.previous (T r).functor (S.page r).d)

/-- Boundaries on a shifted page are contained in its cycles. -/
theorem boundaries_le_cycles (S : ShiftedSpectralSequence T) (r : ℕ+) :
    boundaries S r ≤ cycles S r := sorry

/-- The canonical map from cycles on shifted page `r` to page `r + 1`. -/
@[stacks 0AMI "shifted page cycles-to-next map"]
noncomputable def toNext (S : ShiftedSpectralSequence T) (r : ℕ+) :
    (cycles S r : A) ⟶ (S.page (r + 1)).obj :=
  ShortComplex.Cycles.toHomology (S.page r).shortComplex ≫ (S.iso r).hom

/-- Boundaries on a shifted page vanish under the canonical map to the next page. -/
theorem boundaries_toNext_zero (S : ShiftedSpectralSequence T) (r : ℕ+) :
    Subobject.ofLE (boundaries S r) (cycles S r) (boundaries_le_cycles S r) ≫
        toNext S r = 0 := sorry

/-- The quotient of shifted-page cycles by boundaries is canonically the next page. -/
theorem toNext_isIso (S : ShiftedSpectralSequence T) (r : ℕ+) :
    IsIso
      (cokernel.desc
        (Subobject.ofLE (boundaries S r) (cycles S r) (boundaries_le_cycles S r))
        (toNext S r) (boundaries_toNext_zero S r)) := sorry

end Page

/-- The neutral homology page tower underlying a shifted spectral sequence. -/
@[stacks 0AMI]
noncomputable def homologyPageTower (S : ShiftedSpectralSequence T) : HomologyPageTower A where
  page r := (S.page r).obj
  pageCycle r := Page.cycles S r
  pageBoundary r := Page.boundaries S r
  pageBoundary_le_pageCycle r := Page.boundaries_le_cycles S r
  toNext r := Page.toNext S r
  pageBoundary_toNext_zero r := Page.boundaries_toNext_zero S r
  isIso_descToNext r := Page.toNext_isIso S r

namespace HomologyTower

/-- The complete lattice on the first object of the homology-page tower, transported from the
first shifted page. -/
@[stacks 0AMI "shifted homology-page tower first-page lattice bridge"]
noncomputable abbrev pageOneCompleteLattice (S : ShiftedSpectralSequence T)
    [h : CompleteLattice (Subobject (S.page 1).obj)] :
    CompleteLattice (Subobject (S.homologyPageTower.page 1)) := h

/-- The `r`-th object of the homology page tower is the object of the corresponding shifted
page. -/
@[simp, stacks 0AMI "homology tower page bridge"]
theorem page (S : ShiftedSpectralSequence T) (r : ℕ+) :
    S.homologyPageTower.page r = (S.page r).obj := sorry

/-- The cycle subobject of the homology page tower is the cycle subobject of the shifted page. -/
@[simp, stacks 0AMI "homology tower cycle bridge"]
theorem pageCycle (S : ShiftedSpectralSequence T) (r : ℕ+) :
    S.homologyPageTower.pageCycle r = Page.cycles S r := sorry

/-- The boundary subobject of the homology page tower is the boundary subobject of the shifted
page. -/
@[simp, stacks 0AMI "homology tower boundary bridge"]
theorem pageBoundary (S : ShiftedSpectralSequence T) (r : ℕ+) :
    S.homologyPageTower.pageBoundary r = Page.boundaries S r := sorry

/-- The next-page map of the homology page tower is the canonical shifted cycle-to-next-page
map. -/
@[simp, stacks 0AMI "homology tower transition bridge"]
theorem toNext (S : ShiftedSpectralSequence T) (r : ℕ+) :
    S.homologyPageTower.toNext r = Page.toNext S r := sorry

namespace Map

/-- A shifted-spectral-sequence morphism preserves the cycles on every page. -/
theorem pageCycle_factors
    {S S' : ShiftedSpectralSequence T} (f : S ⟶ S') (r : ℕ+) :
    (S'.homologyPageTower.pageCycle r).Factors
      ((S.homologyPageTower.pageCycle r).arrow ≫ (f.app r).hom) := sorry

/-- A shifted-spectral-sequence morphism preserves the boundaries on every page. -/
theorem pageBoundary_factors
    {S S' : ShiftedSpectralSequence T} (f : S ⟶ S') (r : ℕ+) :
    (S'.homologyPageTower.pageBoundary r).Factors
      ((S.homologyPageTower.pageBoundary r).arrow ≫ (f.app r).hom) := sorry

/-- The restricted page-cycle map commutes with passage to the next shifted page. -/
theorem toNext_comm
    {S S' : ShiftedSpectralSequence T} (f : S ⟶ S') (r : ℕ+) :
    (S'.homologyPageTower.pageCycle r).factorThru
        ((S.homologyPageTower.pageCycle r).arrow ≫ (f.app r).hom)
        (pageCycle_factors f r) ≫ S'.homologyPageTower.toNext r =
      S.homologyPageTower.toNext r ≫ (f.app (r + 1)).hom := sorry

/-- The restricted boundary and cycle maps commute with the page-boundary inclusion.  This is
stored in the induced homology-page-tower morphism so quotient constructions use explicit law
data rather than a deferred global theorem. -/
theorem pageBoundary_map_comp_ofLE
    {S S' : ShiftedSpectralSequence T} (f : S ⟶ S') (r : ℕ+) :
    Subobject.ofLE
        (S.homologyPageTower.pageBoundary r)
        (S.homologyPageTower.pageCycle r)
        (S.homologyPageTower.pageBoundary_le_pageCycle r) ≫
      (S'.homologyPageTower.pageCycle r).factorThru
        ((S.homologyPageTower.pageCycle r).arrow ≫ (f.app r).hom)
        (pageCycle_factors f r) =
      (S'.homologyPageTower.pageBoundary r).factorThru
        ((S.homologyPageTower.pageBoundary r).arrow ≫ (f.app r).hom)
        (pageBoundary_factors f r) ≫
      Subobject.ofLE
        (S'.homologyPageTower.pageBoundary r)
        (S'.homologyPageTower.pageCycle r)
        (S'.homologyPageTower.pageBoundary_le_pageCycle r) := sorry

/-- A shifted-spectral-sequence morphism preserves the recursive cycle stage in the first page. -/
theorem cycle_factors
    {S S' : ShiftedSpectralSequence T} (f : S ⟶ S') (r : ℕ+) :
    (S'.homologyPageTower.cycle r).Factors
      ((S.homologyPageTower.cycle r).arrow ≫ (f.app 1).hom) := sorry

/-- A shifted-spectral-sequence morphism preserves the recursive boundary stage in the first
page. -/
theorem boundary_factors
    {S S' : ShiftedSpectralSequence T} (f : S ⟶ S') (r : ℕ+) :
    (S'.homologyPageTower.boundary r).Factors
      ((S.homologyPageTower.boundary r).arrow ≫ (f.app 1).hom) := sorry

/-- The recursively restricted boundary and cycle maps commute with `B_r ↪ Z_r`. -/
theorem boundary_map_comp_ofLE
    {S S' : ShiftedSpectralSequence T} (f : S ⟶ S') (r : ℕ+) :
    Subobject.ofLE
        (S.homologyPageTower.boundary r)
        (S.homologyPageTower.cycle r)
        (S.homologyPageTower.boundary_le_cycle r) ≫
      (S'.homologyPageTower.cycle r).factorThru
        ((S.homologyPageTower.cycle r).arrow ≫ (f.app 1).hom)
        (cycle_factors f r) =
      (S'.homologyPageTower.boundary r).factorThru
        ((S.homologyPageTower.boundary r).arrow ≫ (f.app 1).hom)
        (boundary_factors f r) ≫
      Subobject.ofLE
        (S'.homologyPageTower.boundary r)
        (S'.homologyPageTower.cycle r)
        (S'.homologyPageTower.boundary_le_cycle r) := sorry

/-- A shifted-spectral-sequence morphism preserves the recursive boundary-cycle intersection
in the first page. -/
theorem intersection_factors
    {S S' : ShiftedSpectralSequence T} (f : S ⟶ S') (r : ℕ+) :
    (S'.homologyPageTower.boundary r ⊓ S'.homologyPageTower.cycle r).Factors
      ((S.homologyPageTower.boundary r ⊓ S.homologyPageTower.cycle r).arrow ≫
        (f.app 1).hom) := sorry

/-- The restricted recursive intersection and cycle maps of a shifted-spectral-sequence
morphism commute with the inclusion into the cycle stage. -/
theorem intersection_map_comp_ofLE
    {S S' : ShiftedSpectralSequence T} (f : S ⟶ S') (r : ℕ+) :
    Subobject.ofLE
        (S.homologyPageTower.boundary r ⊓ S.homologyPageTower.cycle r)
        (S.homologyPageTower.cycle r)
        _root_.inf_le_right ≫
      (S'.homologyPageTower.cycle r).factorThru
        ((S.homologyPageTower.cycle r).arrow ≫ (f.app 1).hom)
        (cycle_factors f r) =
      (S'.homologyPageTower.boundary r ⊓ S'.homologyPageTower.cycle r).factorThru
        ((S.homologyPageTower.boundary r ⊓ S.homologyPageTower.cycle r).arrow ≫
          (f.app 1).hom)
        (intersection_factors f r) ≫
      Subobject.ofLE
        (S'.homologyPageTower.boundary r ⊓ S'.homologyPageTower.cycle r)
        (S'.homologyPageTower.cycle r)
        _root_.inf_le_right := sorry

end Map

/-- The homology-page-tower morphism induced by a shifted-spectral-sequence morphism. -/
@[stacks 0AMI "homology-page tower morphism"]
noncomputable def map
    {S S' : ShiftedSpectralSequence T} (f : S ⟶ S') :
    S.homologyPageTower ⟶ S'.homologyPageTower where
  app r := (f.app r).hom
  pageCycle_factors r := Map.pageCycle_factors f r
  pageBoundary_factors r := Map.pageBoundary_factors f r
  toNext_comm r := Map.toNext_comm f r
  pageBoundary_map_comp_ofLE r := Map.pageBoundary_map_comp_ofLE f r
  cycle_factors r := Map.cycle_factors f r
  boundary_factors r := Map.boundary_factors f r
  boundary_map_comp_ofLE r := Map.boundary_map_comp_ofLE f r
  intersection_factors r := Map.intersection_factors f r
  intersection_map_comp_ofLE r := Map.intersection_map_comp_ofLE f r

/-- The component of the induced homology-page-tower map is the underlying component of the
shifted-spectral-sequence morphism. -/
@[simp]
theorem map_app
    {S S' : ShiftedSpectralSequence T} (f : S ⟶ S') (r : ℕ+) :
    (map f).app r = (f.app r).hom := sorry

/-- The induced homology-page-tower map preserves identities. -/
theorem map_id (S : ShiftedSpectralSequence T) :
    map (𝟙 S) = 𝟙 S.homologyPageTower := sorry

/-- The induced homology-page-tower map preserves composition. -/
theorem map_comp {S S' S'' : ShiftedSpectralSequence T}
    (f : S ⟶ S') (g : S' ⟶ S'') :
    map (f ≫ g) = map f ≫ map g := sorry

/-- A shifted spectral sequence determines a homology page tower functorially. -/
@[stacks 0AMI "homology-page tower functor"]
noncomputable def functor (T : ℕ+ → (A ≌ A)) :
  ShiftedSpectralSequence T ⥤ HomologyPageTower A where
  obj S := S.homologyPageTower
  map f := HomologyTower.map f
  map_id S := HomologyTower.map_id S
  map_comp f g := HomologyTower.map_comp f g

/-- Evaluation of the shifted homology-page-tower functor on an object is its tower. -/
@[simp]
theorem Functor.obj (T : ℕ+ → (A ≌ A))
    (S : ShiftedSpectralSequence T) :
    (functor T).obj S = S.homologyPageTower := sorry

/-- Evaluation of the shifted homology-page-tower functor on a morphism is the induced tower map. -/
@[simp]
theorem Functor.map (T : ℕ+ → (A ≌ A))
    {S S' : ShiftedSpectralSequence T} (f : S ⟶ S') :
    (functor T).map f = map f := sorry

end HomologyTower

/-! ## Cycle and boundary filtrations -/

/-- A zero-based recursive cycle stage inside the first shifted page. -/
abbrev CycleStage (S : ShiftedSpectralSequence T) (n : ℕ) :=
  HomologyPageTower.CycleStage S.homologyPageTower n

/-- The recursively constructed cycle stage inside the first shifted page. -/
noncomputable abbrev cycleStage (S : ShiftedSpectralSequence T) (n : ℕ) : CycleStage S n :=
  S.homologyPageTower.cycleStage n

/-- The recursively constructed boundary stage inside the first shifted page. -/
noncomputable abbrev boundaryStage (S : ShiftedSpectralSequence T) (n : ℕ) :
    Subobject (S.page 1).obj :=
  S.homologyPageTower.boundaryStage n

/-- The cycle subobject `Z_r ≤ E₁` of a shifted spectral sequence. -/
@[stacks 0AMI]
abbrev cycle (S : ShiftedSpectralSequence T) (r : ℕ+) : Subobject (S.page 1).obj :=
  S.homologyPageTower.cycle r

/-- The boundary subobject `B_r ≤ E₁` of a shifted spectral sequence. -/
@[stacks 0AMI]
abbrev boundary (S : ShiftedSpectralSequence T) (r : ℕ+) : Subobject (S.page 1).obj :=
  S.homologyPageTower.boundary r

/-- On the first page, the cycle subobject is the top subobject. -/
theorem cycle_one (S : ShiftedSpectralSequence T) : S.cycle 1 = ⊤ := sorry

/-- On the first page, the boundary subobject is the bottom subobject. -/
theorem boundary_one (S : ShiftedSpectralSequence T) : S.boundary 1 = ⊥ := sorry

/-- Every recursive boundary stage is contained in the corresponding cycle stage. -/
theorem boundary_le_cycle (S : ShiftedSpectralSequence T) (r : ℕ+) :
    S.boundary r ≤ S.cycle r := sorry

/-- The canonical map `Z_r ⟶ E_r`. -/
@[stacks 0AMI "shifted recursive cycle-to-page map"]
noncomputable abbrev cycleToPage (S : ShiftedSpectralSequence T) (r : ℕ+) :
    (S.cycle r : A) ⟶ (S.page r).obj :=
  S.homologyPageTower.cycleToPage r

/-- On the first shifted page, `cycleToPage` is the cycle inclusion. -/
theorem Cycle.toPage_one (S : ShiftedSpectralSequence T) :
    S.cycleToPage 1 = (S.cycle 1).arrow := sorry

namespace Cycle

/-- The successor cycle is the pullback of the current page cycles, mapped into page one. -/
@[stacks 0AMI "successor cycle pullback"]
theorem succ_eq_pullback (S : ShiftedSpectralSequence T) (r : ℕ+) :
    S.cycle (r + 1) =
      (Subobject.map (S.cycle r).arrow).obj
        ((Subobject.pullback (S.cycleToPage r)).obj (Page.cycles S r)) := sorry

end Cycle

namespace Boundary

/-- The successor boundary is the pullback of the current page boundaries, mapped into page one. -/
@[stacks 0AMI "successor boundary pullback"]
theorem succ_eq_pullback (S : ShiftedSpectralSequence T) (r : ℕ+) :
    S.boundary (r + 1) =
      (Subobject.map (S.cycle r).arrow).obj
        ((Subobject.pullback (S.cycleToPage r)).obj (Page.boundaries S r)) := sorry

end Boundary

/-- Every recursive cycle-to-page map is an epimorphism. -/
instance Cycle.toPage_epi (S : ShiftedSpectralSequence T) (r : ℕ+) :
    Epi (S.cycleToPage r) := sorry

/-- The map `Z_r ⟶ E_r` kills the included boundary subobject. -/
theorem Boundary.toPage_zero (S : ShiftedSpectralSequence T) (r : ℕ+) :
    Subobject.ofLE (S.boundary r) (S.cycle r) (S.boundary_le_cycle r) ≫
      S.cycleToPage r = 0 := sorry

/-! ## Filtration order and functoriality -/

/-- Successor cycle subobjects form a descending chain. -/
theorem Cycle.succ_le (S : ShiftedSpectralSequence T) (r : ℕ+) :
    S.cycle (r + 1) ≤ S.cycle r := sorry

/-- Successor boundary subobjects form an ascending chain. -/
theorem Boundary.le_succ (S : ShiftedSpectralSequence T) (r : ℕ+) :
    S.boundary r ≤ S.boundary (r + 1) := sorry

/-- The boundary filtration is monotone in the page index. -/
theorem Boundary.monotone (S : ShiftedSpectralSequence T) :
    ∀ ⦃r s : ℕ+⦄, r ≤ s → S.boundary r ≤ S.boundary s := sorry

/-- The cycle filtration is antitone in the page index. -/
theorem Cycle.antitone (S : ShiftedSpectralSequence T) :
    ∀ ⦃r s : ℕ+⦄, r ≤ s → S.cycle s ≤ S.cycle r := sorry

/-- Every boundary stage lies in every cycle stage. -/
theorem Boundary.le_cycle (S : ShiftedSpectralSequence T) (r s : ℕ+) :
    S.boundary r ≤ S.cycle s := sorry

/-- A morphism of shifted spectral sequences maps cycle stages into cycle stages. -/
theorem Cycle.map_le {S S' : ShiftedSpectralSequence T} (f : S ⟶ S') (r : ℕ+) :
    (Subobject.exists (f.app 1).hom).obj (S.cycle r) ≤ S'.cycle r := sorry

/-- A morphism of shifted spectral sequences maps boundary stages into boundary stages. -/
theorem Boundary.map_le {S S' : ShiftedSpectralSequence T} (f : S ⟶ S') (r : ℕ+) :
    (Subobject.exists (f.app 1).hom).obj (S.boundary r) ≤ S'.boundary r := sorry

/-- The map induced by a shifted-spectral-sequence morphism between cycle stages. -/
@[stacks 0AMI "shifted recursive cycle map"]
noncomputable def Cycle.map
    {S S' : ShiftedSpectralSequence T} (f : S ⟶ S') (r : ℕ+) :
    (S.cycle r : A) ⟶ (S'.cycle r : A) :=
  HomologyPageTower.Cycle.map (HomologyTower.map f) r

/-- The map induced by a shifted-spectral-sequence morphism between boundary stages. -/
@[stacks 0AMI "shifted recursive boundary map"]
noncomputable def Boundary.map
    {S S' : ShiftedSpectralSequence T} (f : S ⟶ S') (r : ℕ+) :
    (S.boundary r : A) ⟶ (S'.boundary r : A) :=
  HomologyPageTower.Boundary.map (HomologyTower.map f) r

/-- The induced cycle map recovers the first-page component after inclusion. -/
@[reassoc (attr := simp)]
theorem Cycle.map_arrow
    {S S' : ShiftedSpectralSequence T} (f : S ⟶ S') (r : ℕ+) :
    Cycle.map f r ≫ (S'.cycle r).arrow = (S.cycle r).arrow ≫ (f.app 1).hom := sorry

/-- The induced boundary map recovers the first-page component after inclusion. -/
@[reassoc (attr := simp)]
theorem Boundary.map_arrow
    {S S' : ShiftedSpectralSequence T} (f : S ⟶ S') (r : ℕ+) :
    Boundary.map f r ≫ (S'.boundary r).arrow =
      (S.boundary r).arrow ≫ (f.app 1).hom := sorry

/-- The induced cycle map commutes with the canonical maps to shifted page `r`. -/
@[reassoc]
theorem Cycle.toPage_naturality
    {S S' : ShiftedSpectralSequence T} (f : S ⟶ S') (r : ℕ+) :
    Cycle.map f r ≫ S'.cycleToPage r = S.cycleToPage r ≫ (f.app r).hom := sorry

/-- Proof-free eventual boundary and cycle data for a shifted spectral sequence. -/
@[stacks 0AMI "explicit shifted spectral-sequence limit-stage data"]
abbrev LimitStages.Data (S : ShiftedSpectralSequence T) :=
  HomologyPageTower.LimitStages.Data S.homologyPageTower

/-- Complete eventual boundary and cycle data for a shifted spectral sequence. -/
@[stacks 0AMI "shifted spectral-sequence limit stages"]
abbrev LimitStages (S : ShiftedSpectralSequence T) :=
  HomologyPageTower.LimitStages S.homologyPageTower

namespace LimitStages

variable {S : ShiftedSpectralSequence T}

/-- Forget the universal-property proofs from complete shifted limit stages. -/
@[stacks 0AMI "proof-free shifted limit-stage data"]
abbrev toData (L : LimitStages S) : LimitStages.Data S :=
  HomologyPageTower.LimitStages.toData L

/-- The proof-free infinity-page representative selected by complete shifted limit stages. -/
@[stacks 0AMI "infinity page from complete shifted limit stages"]
noncomputable abbrev infinityPage (L : LimitStages S) : A :=
  HomologyPageTower.LimitStages.infinityPage L

namespace InfinityPage

/-- The canonical projection from a complete shifted limit stage to its infinity-page
representative. -/
@[stacks 0AMI "shifted limit-stage infinity-page projection"]
noncomputable abbrev π (L : LimitStages S) :
    (L.cycle : A) ⟶ L.infinityPage :=
  HomologyPageTower.LimitStages.InfinityPage.π L

end InfinityPage

/-- Complete shifted first-page subobject lattices provide canonical shifted limit stages. -/
@[stacks 0AMI "canonical shifted spectral-sequence limit stages"]
noncomputable def canonical (S : ShiftedSpectralSequence T)
    [CompleteLattice (Subobject (S.page 1).obj)] : LimitStages S :=
  @HomologyPageTower.LimitStages.canonical _ _ _ S.homologyPageTower
    (HomologyTower.pageOneCompleteLattice S)

/-- The boundary component of canonical shifted limit stages is the existing eventual boundary. -/
@[simp, stacks 0AMI "canonical shifted limit boundary"]
theorem canonical_boundary (S : ShiftedSpectralSequence T)
    [CompleteLattice (Subobject (S.page 1).obj)] :
    (canonical S).boundary =
      @HomologyPageTower.boundaryInfinity _ _ _ S.homologyPageTower
        (HomologyTower.pageOneCompleteLattice S) := sorry

/-- The cycle component of canonical shifted limit stages is the existing eventual cycle. -/
@[simp, stacks 0AMI "canonical shifted limit cycle"]
theorem canonical_cycle (S : ShiftedSpectralSequence T)
    [CompleteLattice (Subobject (S.page 1).obj)] :
    (canonical S).cycle =
      @HomologyPageTower.cycleInfinity _ _ _ S.homologyPageTower
        (HomologyTower.pageOneCompleteLattice S) := sorry

end LimitStages

section Infinity

/-- The eventual cycle subobject `Z_infinity`. -/
@[stacks 0AMI "shifted eventual cycle subobject"]
noncomputable abbrev cycleInfinity (S : ShiftedSpectralSequence T)
    [CompleteLattice (Subobject (S.page 1).obj)] :
    Subobject (S.page 1).obj :=
  @HomologyPageTower.cycleInfinity _ _ _ S.homologyPageTower
    (HomologyTower.pageOneCompleteLattice S)

/-- The eventual boundary subobject `B_infinity`. -/
@[stacks 0AMI "shifted eventual boundary subobject"]
noncomputable abbrev boundaryInfinity (S : ShiftedSpectralSequence T)
    [CompleteLattice (Subobject (S.page 1).obj)] :
    Subobject (S.page 1).obj :=
  @HomologyPageTower.boundaryInfinity _ _ _ S.homologyPageTower
    (HomologyTower.pageOneCompleteLattice S)

namespace InfinityPage

/-- Eventual boundaries are contained in eventual cycles. -/
theorem boundary_le_cycle (S : ShiftedSpectralSequence T)
    [CompleteLattice (Subobject (S.page 1).obj)] :
    S.boundaryInfinity ≤ S.cycleInfinity := sorry

end InfinityPage

/-- The infinity-page object `Z_infinity / B_infinity`. -/
@[stacks 0AMI]
noncomputable abbrev infinityPage (S : ShiftedSpectralSequence T)
    [CompleteLattice (Subobject (S.page 1).obj)] : A :=
  @HomologyPageTower.infinityPage _ _ _ S.homologyPageTower
    (HomologyTower.pageOneCompleteLattice S)

namespace InfinityPage

/-- The canonical projection from eventual cycles to the proof-free infinity-page entry. -/
@[stacks 0AMI]
noncomputable abbrev π (S : ShiftedSpectralSequence T)
    [CompleteLattice (Subobject (S.page 1).obj)] :
    (S.cycleInfinity : A) ⟶ S.infinityPage :=
  @HomologyPageTower.InfinityPage.π _ _ _ S.homologyPageTower
    (HomologyTower.pageOneCompleteLattice S)

/-- The proof-free infinity-page entry is isomorphic to the textbook quotient once eventual
boundary containment is available. -/
@[stacks 0AMI]
theorem isIsomorphic (S : ShiftedSpectralSequence T)
    [CompleteLattice (Subobject (S.page 1).obj)] :
    IsIsomorphic S.infinityPage
      (cokernel
        (Subobject.ofLE S.boundaryInfinity S.cycleInfinity
          (boundary_le_cycle S))) := sorry

end InfinityPage

end Infinity

end ShiftedSpectralSequence

end CategoryTheory
