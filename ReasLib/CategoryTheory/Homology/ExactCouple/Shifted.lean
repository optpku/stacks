/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.SpectralSequence.Shifted
public import ReasLib.CategoryTheory.Homology.ShortComplex.Cycles
public import ReasLib.CategoryTheory.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Shifted Exact Couples

This module develops exact couples for a pair of shift autoequivalences. It constructs the
derived couple explicitly and packages its iterates as a spectral sequence with page-dependent
shift.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

section Definition

variable [HasZeroMorphisms C]

/-- 0AMJ (Remark 12.21.5, Variant): for shift autoequivalences `S` and `T`, a shifted exact couple
is the exact complex `T E ⟶ T A ⟶ A ⟶ S E ⟶ S A`, recorded by its two objects and three
generating maps. The adjoint form `α : A ⟶ T⁻¹ A` is recovered from `tAlpha : T A ⟶ A`. -/
@[stacks 0AMJ]
structure ShiftedExactCouple (S T : C ≌ C) where
  /-- The outer object. -/
  A : C
  /-- The page object. -/
  E : C
  /-- The translated outer map `T A ⟶ A`. -/
  tAlpha : T.functor.obj A ⟶ A
  /-- The map from the page object to the outer object. -/
  f : E ⟶ A
  /-- The connecting map from the outer object to the shifted page object. -/
  g : A ⟶ S.functor.obj E
  /-- The composite `T f ≫ tAlpha` vanishes. -/
  Tf_comp_tAlpha : T.functor.map f ≫ tAlpha = 0
  /-- The composite `tAlpha ≫ g` vanishes. -/
  tAlpha_comp_g : tAlpha ≫ g = 0
  /-- The composite `g ≫ S f` vanishes. -/
  g_comp_Sf : g ≫ S.functor.map f = 0
  /-- Exactness at `T A`. -/
  exact_Tf_tAlpha :
    (ShortComplex.mk (T.functor.map f) tAlpha Tf_comp_tAlpha).Exact
  /-- Exactness at `A`. -/
  exact_tAlpha_g :
    (ShortComplex.mk tAlpha g tAlpha_comp_g).Exact
  /-- Exactness at `S E`. -/
  exact_g_Sf :
    (ShortComplex.mk g (S.functor.map f) g_comp_Sf).Exact

end Definition

section Basic

variable [HasZeroMorphisms C]

namespace ShiftedExactCouple

variable {S T : C ≌ C} (X : ShiftedExactCouple S T)

/-- The page-one differential `E ⟶ S E`. -/
@[stacks 0AMJ "shifted exact-couple page differential"]
abbrev d : X.E ⟶ S.functor.obj X.E :=
  X.f ≫ X.g

/-- The adjoint form `A ⟶ T⁻¹ A` of the translated outer map. -/
@[stacks 0AMJ "shifted exact-couple adjoint outer map"]
abbrev α : X.A ⟶ T.inverse.obj X.A :=
  (T.toAdjunction.homEquiv X.A X.A) X.tAlpha

/-- The page-one shifted differential squares to zero. -/
@[stacks 0AMJ "shifted exact-couple page differential square"]
theorem d_squared : X.d ≫ S.functor.map X.d = 0 := by
  simp only [d, Functor.map_comp, Category.assoc]
  rw [← Category.assoc X.g, X.g_comp_Sf, zero_comp, comp_zero]

/-- The explicit page differential object associated to a supplied square-zero witness. -/
@[stacks 0AMJ "page differential object with square-zero witness"]
abbrev pageOf (X : ShiftedExactCouple S T) (dSquared : X.d ≫ S.functor.map X.d = 0) :
    ShiftedDifferentialObject S.functor where
  obj := X.E
  d := X.d
  d_squared := dSquared

/-- The underlying object of `pageOf` is the page object of the shifted exact couple. -/
@[simp]
theorem pageOf_obj (X : ShiftedExactCouple S T) (dSquared : X.d ≫ S.functor.map X.d = 0) :
    (X.pageOf dSquared).obj = X.E := sorry

/-- The shifted differential of `pageOf` is the page-one differential of the shifted exact
couple. -/
@[simp]
theorem pageOf_d (X : ShiftedExactCouple S T) (dSquared : X.d ≫ S.functor.map X.d = 0) :
    (X.pageOf dSquared).d = X.d := sorry

/-- The explicit page short complex associated to a supplied zero-composite witness for the
translated previous differential and the page differential. -/
@[stacks 0AMJ "page short complex with zero-composite witness"]
noncomputable abbrev pageShortComplexOf (X : ShiftedExactCouple S T)
    (previousCompD : ShiftedDifferentialObject.Differential.previous S.functor X.d ≫ X.d = 0) :
    ShortComplex C :=
  ShiftedDifferentialObject.Differential.shortComplexOfZero S.functor X.d previousCompD

/-- The canonical shifted differential object carried by the page-one differential. -/
@[stacks 0AMJ "canonical page differential object"]
def page (X : ShiftedExactCouple S T) : ShiftedDifferentialObject S.functor :=
  X.pageOf X.d_squared

/-- A morphism between shifted exact couples with fixed source and target shifts. -/
@[ext, stacks 0AMJ "shifted exact-couple morphism"]
structure Hom (X Y : ShiftedExactCouple S T) where
  /-- The component on the outer objects. -/
  a : X.A ⟶ Y.A
  /-- The component on the page objects. -/
  e : X.E ⟶ Y.E
  /-- Compatibility with the translated outer maps. -/
  comm_tAlpha : T.functor.map a ≫ Y.tAlpha = X.tAlpha ≫ a
  /-- Compatibility with the maps from the page objects. -/
  comm_f : X.f ≫ a = e ≫ Y.f
  /-- Compatibility with the maps to the shifted page objects. -/
  comm_g : X.g ≫ S.functor.map e = a ≫ Y.g

namespace Hom

/-- The identity morphism of a shifted exact couple. -/
def id (X : ShiftedExactCouple S T) : Hom X X where
  a := 𝟙 X.A
  e := 𝟙 X.E
  comm_tAlpha := sorry
  comm_f := sorry
  comm_g := sorry

/-- The composite of two shifted-exact-couple morphisms. -/
def comp {X Y Z : ShiftedExactCouple S T} (φ : Hom X Y) (ψ : Hom Y Z) : Hom X Z where
  a := φ.a ≫ ψ.a
  e := φ.e ≫ ψ.e
  comm_tAlpha := sorry
  comm_f := sorry
  comm_g := sorry

end Hom

/-- Shifted exact couples with fixed shifts form a category. -/
instance : Category (ShiftedExactCouple S T) where
  Hom X Y := Hom X Y
  id := Hom.id
  comp φ ψ := Hom.comp φ ψ
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- A shifted-exact-couple morphism commutes with the adjoint outer maps. -/
@[stacks 0AMJ "adjoint outer-map compatibility"]
theorem Hom.comm_α {X Y : ShiftedExactCouple S T} (φ : Hom X Y) :
    φ.a ≫ Y.α = X.α ≫ T.inverse.map φ.a := sorry

/-- The page component of a shifted-exact-couple morphism commutes with page differentials. -/
@[reassoc]
theorem Hom.e_comp_d {X Y : ShiftedExactCouple S T} (φ : Hom X Y) :
    φ.e ≫ Y.d = X.d ≫ S.functor.map φ.e := sorry

/-- A shifted-exact-couple morphism induces a morphism between page differential objects built
from explicitly supplied square-zero witnesses. -/
@[stacks 0AMJ "page map with square-zero witnesses"]
def Hom.pageMapOf {X Y : ShiftedExactCouple S T} (φ : Hom X Y)
    (dSquaredX : X.d ≫ S.functor.map X.d = 0) (dSquaredY : Y.d ≫ S.functor.map Y.d = 0) :
    X.pageOf dSquaredX ⟶ Y.pageOf dSquaredY where
  hom := φ.e
  comm := φ.e_comp_d

/-- The underlying map of `pageMapOf` is the page component of the shifted exact-couple
morphism. -/
@[simp]
theorem Hom.pageMapOf_hom {X Y : ShiftedExactCouple S T} (φ : Hom X Y)
    (dSquaredX : X.d ≫ S.functor.map X.d = 0) (dSquaredY : Y.d ≫ S.functor.map Y.d = 0) :
    (φ.pageMapOf dSquaredX dSquaredY).hom = φ.e := sorry

/-- A shifted-exact-couple morphism induces a morphism of its canonical page differential
objects. -/
@[stacks 0AMJ "canonical page map"]
def Hom.pageMap {X Y : ShiftedExactCouple S T} (φ : Hom X Y) : X.page ⟶ Y.page :=
  φ.pageMapOf X.d_squared Y.d_squared

/-- The underlying map of the canonical page map is the page component. -/
@[simp]
theorem Hom.pageMap_hom {X Y : ShiftedExactCouple S T} (φ : Hom X Y) :
    φ.pageMap.hom = φ.e := sorry

namespace PageMap

/-- Induced page maps preserve identity morphisms. -/
@[simp]
theorem id (X : ShiftedExactCouple S T) :
    (𝟙 X : X ⟶ X).pageMap = 𝟙 X.page := sorry

/-- Induced page maps preserve composition. -/
@[simp]
theorem comp {X Y Z : ShiftedExactCouple S T} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    (φ ≫ ψ).pageMap = φ.pageMap ≫ ψ.pageMap := sorry

end PageMap

/-- The functor sending a shifted exact couple to its page-one shifted differential object. -/
@[stacks 0AMJ "page differential functor"]
noncomputable def pageFunctor (S T : C ≌ C) :
    ShiftedExactCouple S T ⥤ ShiftedDifferentialObject S.functor where
  obj X := X.page
  map φ := φ.pageMap
  map_id := sorry
  map_comp := sorry

namespace PageFunctor

/-- The shifted exact-couple page functor evaluates to the canonical page differential object. -/
@[simp]
theorem obj (X : ShiftedExactCouple S T) :
    (pageFunctor S T).obj X = X.page := sorry

/-- The shifted exact-couple page functor maps a morphism to its induced page map. -/
@[simp]
theorem map {X Y : ShiftedExactCouple S T} (φ : X ⟶ Y) :
    (pageFunctor S T).map φ = φ.pageMap := sorry

end PageFunctor

end ShiftedExactCouple

end Basic

section Derived

variable [Abelian C]

namespace ShiftedExactCouple

variable {S T : C ≌ C} (X : ShiftedExactCouple S T)

/-! ## Derived-couple data -/

namespace Derived

/-- The outer object of a derived shifted exact couple. -/
@[stacks 0AMJ "derived outer object"]
abbrev outer : C :=
  image X.tAlpha

/-- The translated outer map `T A' ⟶ A'` on the image of `tAlpha`. -/
@[stacks 0AMJ "derived translated outer map"]
noncomputable def tAlpha : T.functor.obj (outer X) ⟶ outer X :=
  (PreservesImage.iso T.functor X.tAlpha).inv ≫
    image.map (Arrow.homMk' _ _)

/-- The derived translated outer map commutes with the image inclusion. -/
theorem tAlpha_comp_ι :
    tAlpha X ≫ image.ι X.tAlpha =
      T.functor.map (image.ι X.tAlpha) ≫ X.tAlpha := sorry

/-- Concrete data needed to construct the maps of one derived shifted exact couple.

The fields that are maps or objects are supplied explicitly.  `Laws` records the source-level
comparison and exactness statements separately, so no concrete map is constructed from an
unproved universal-property side condition. -/
@[stacks 0AMJ "derived shifted exact-couple data"]
structure Data (X : ShiftedExactCouple S T) where
  /-- The map from page cycles to the derived outer object. -/
  fCycles : (X.page.shortComplex).cycles ⟶ outer X
  /-- The cycle map vanishes on page boundaries. -/
  fCycles_zero : (X.page.shortComplex).toCycles ≫ fCycles = 0
  /-- The source-level representative of the derived connecting map. -/
  gFromOuter : T.functor.obj X.A ⟶
    (S.trans T).functor.obj (X.page.shortComplex).homology
  /-- The source representative vanishes after the translated map `f`. -/
  map_f_gFromOuter_zero : T.functor.map X.f ≫ gFromOuter = 0

namespace Data

variable {S T : C ≌ C} {X : ShiftedExactCouple S T}

/-- Square-zero is a property of the input shifted exact couple. -/
theorem dSquared (D : Data X) : X.d ≫ S.functor.map X.d = 0 := X.d_squared

/-- The previous differential composes to zero by the canonical shifted-page construction. -/
theorem previousCompD (D : Data X) :
    ShiftedDifferentialObject.Differential.previous S.functor X.d ≫ X.d = 0 :=
  ShiftedDifferentialObject.Differential.comp S.functor X.d X.d_squared

/-- The page differential object retained by a package of derived-couple data. -/
@[stacks 0AMJ "derived shifted page differential object"]
abbrev page (D : Data X) : ShiftedDifferentialObject S.functor :=
  X.page

/-- The explicitly retained page short complex. -/
@[stacks 0AMJ "derived shifted page short complex"]
noncomputable abbrev shortComplex (D : Data X) : ShortComplex C :=
  X.page.shortComplex

/-- The homology object used as the page object of the derived shifted exact couple. -/
@[stacks 0AMJ "derived shifted page object"]
noncomputable abbrev homology (D : Data X) : C :=
  D.shortComplex.homology

/-- The canonical short complex carried by the retained page object agrees with the explicitly
retained short complex. -/
@[simp, stacks 0AMJ "derived shifted page short-complex bridge"]
theorem page_shortComplex (D : Data X) : D.page.shortComplex = D.shortComplex := sorry

/-- The canonical homology of the retained page object agrees with the explicitly retained
derived page object. -/
@[simp, stacks 0AMJ "derived shifted page-object bridge"]
theorem page_homology (D : Data X) : D.page.homology = D.homology := sorry

/-- The mapped short complex whose homology receives the source-level connecting representative. -/
noncomputable abbrev mappedShortComplex (D : Data X) : ShortComplex C :=
  (S.trans T).functor.mapShortComplex.obj D.shortComplex

end Data

variable {S T : C ≌ C} {X : ShiftedExactCouple S T}

/-- The map from the retained page homology to the derived outer object. -/
@[stacks 0AMJ "derived shifted f map"]
noncomputable def f (D : Data X) : D.homology ⟶ outer X :=
  D.shortComplex.descHomology D.fCycles D.fCycles_zero

/-- The map from the derived outer object to the shifted retained page homology. -/
@[stacks 0AMJ "derived shifted g map"]
noncomputable def g (D : Data X) :
    outer X ⟶ (S.trans T).functor.obj D.homology :=
  X.exact_Tf_tAlpha.isColimitImage.desc
    (CokernelCofork.ofπ D.gFromOuter D.map_f_gFromOuter_zero)

/-- Proposition-valued laws certifying that `Data` has the standard derived shifted-exact-couple
meaning for the input exact couple. -/
@[stacks 0AMJ "derived shifted exact-couple laws"]
structure Laws (D : Data X) : Prop where
  /-- The cycle representative for the derived `f` agrees with the original `f` after inclusion
  into `A`. -/
  fCycles_comp_ι : D.fCycles ≫ image.ι X.tAlpha = D.shortComplex.iCycles ≫ X.f
  /-- The translated map `T g` is a cycle in the mapped page short complex. -/
  map_g_cycles : T.functor.map X.g ≫ D.mappedShortComplex.g = 0
  /-- The selected source representative is the homology class of `T g`. -/
  gFromOuter_eq_lift : D.gFromOuter =
    D.mappedShortComplex.liftToHomology (T.functor.map X.g) map_g_cycles ≫
      (D.shortComplex.mapHomologyIso (S.trans T).functor).hom
  /-- The derived maps satisfy the first zero-composite relation. -/
  map_f_comp_tAlpha : T.functor.map (f D) ≫ tAlpha X = 0
  /-- The derived maps satisfy the second zero-composite relation. -/
  tAlpha_comp_g : tAlpha X ≫ g D = 0
  /-- The derived maps satisfy the third zero-composite relation. -/
  g_comp_map_f : g D ≫ (S.trans T).functor.map (f D) = 0
  /-- Exactness at the translated derived outer object. -/
  exact_map_f_tAlpha :
    (ShortComplex.mk (T.functor.map (f D)) (tAlpha X) map_f_comp_tAlpha).Exact
  /-- Exactness at the derived outer object. -/
  exact_tAlpha_g :
    (ShortComplex.mk (tAlpha X) (g D) tAlpha_comp_g).Exact
  /-- Exactness at the shifted derived page object. -/
  exact_g_map_f :
    (ShortComplex.mk (g D) ((S.trans T).functor.map (f D)) g_comp_map_f).Exact

/-- The derived `f` is represented on cycles by the original map `f`. -/
@[stacks 0AMJ "derived shifted f representative"]
theorem f_spec (D : Data X) (hD : Laws D) :
    D.shortComplex.homologyπ ≫ f D = D.fCycles := sorry

/-- The derived `g` descends from the selected source-level representative. -/
@[stacks 0AMJ "derived shifted g representative"]
theorem g_spec (D : Data X) (hD : Laws D) :
    factorThruImage X.tAlpha ≫ g D = D.gFromOuter := sorry

/-- The derived `g` is represented by the shifted homology class of the original map `g`. -/
@[stacks 0AMJ "derived shifted g cycle representative"]
theorem g_spec_lift (D : Data X) (hD : Laws D) :
    factorThruImage X.tAlpha ≫ g D =
      D.mappedShortComplex.liftToHomology (T.functor.map X.g) hD.map_g_cycles ≫
        (D.shortComplex.mapHomologyIso (S.trans T).functor).hom := sorry

/-- Assemble a derived shifted exact couple from explicit data and its certified laws. -/
@[stacks 0AMJ]
noncomputable def ofData (D : Data X) (hD : Laws D) :
    ShiftedExactCouple (S.trans T) T where
  A := outer X
  E := D.homology
  tAlpha := tAlpha X
  f := f D
  g := g D
  Tf_comp_tAlpha := hD.map_f_comp_tAlpha
  tAlpha_comp_g := hD.tAlpha_comp_g
  g_comp_Sf := hD.g_comp_map_f
  exact_Tf_tAlpha := hD.exact_map_f_tAlpha
  exact_tAlpha_g := hD.exact_tAlpha_g
  exact_g_Sf := hD.exact_g_map_f

/-- Factor the original `f` on page cycles through `image (Tα) = kernel g`. -/
noncomputable def cyclesToOuter (X : ShiftedExactCouple S T) :
    X.page.shortComplex.cycles ⟶ outer X :=
  X.exact_tAlpha_g.isLimitImage'.lift
    (KernelFork.ofι (X.page.shortComplex.iCycles ≫ X.f) (by
      rw [Category.assoc]
      exact X.page.shortComplex.iCycles_g))

/-- The image factorization retains the original map on cycle representatives. -/
@[reassoc]
theorem cyclesToOuter_comp_ι (X : ShiftedExactCouple S T) :
    cyclesToOuter X ≫ image.ι X.tAlpha = X.page.shortComplex.iCycles ≫ X.f := by
  exact Fork.IsLimit.lift_ι _

/-- The translated original `g` is a cycle in the translated page short complex. -/
theorem map_g_cycles (X : ShiftedExactCouple S T) :
    T.functor.map X.g ≫
      ((S.trans T).functor.mapShortComplex.obj X.page.shortComplex).g = 0 := by
  change T.functor.map X.g ≫ T.functor.map (S.functor.map X.d) = 0
  rw [← T.functor.map_comp]
  change T.functor.map (X.g ≫ S.functor.map (X.f ≫ X.g)) = 0
  rw [S.functor.map_comp, ← Category.assoc, X.g_comp_Sf, zero_comp,
    Functor.map_zero]

/-- The homology class of `T g`, transported through the homology preservation isomorphism
of the supplied equivalences. -/
noncomputable def outerToHomology (X : ShiftedExactCouple S T) :
    T.functor.obj X.A ⟶ (S.trans T).functor.obj X.page.homology :=
  ((S.trans T).functor.mapShortComplex.obj X.page.shortComplex).liftToHomology
      (T.functor.map X.g) (map_g_cycles X) ≫
    (X.page.shortComplex.mapHomologyIso (S.trans T).functor).hom

/-- The previous page differential is killed by `f`. -/
theorem previous_comp_f (X : ShiftedExactCouple S T) :
    X.page.shortComplex.f ≫ X.f = 0 := by
  apply S.functor.map_injective
  rw [Functor.map_comp, Functor.map_zero, ShiftedDifferentialObject.Differential.map]
  change (S.functor.asEquivalence.counit.app X.E ≫ (X.f ≫ X.g)) ≫
    S.functor.map X.f = 0
  simp only [Category.assoc, X.g_comp_Sf, comp_zero]

/-- `T f ≫ T g` has an explicit boundary representative in the mapped page complex. -/
theorem map_f_map_g_boundary (X : ShiftedExactCouple S T) :
    T.functor.map X.f ≫ T.functor.map X.g =
      T.functor.map (S.functor.asEquivalence.counitInv.app X.E) ≫
        ((S.trans T).functor.mapShortComplex.obj X.page.shortComplex).f := by
  change T.functor.map X.f ≫ T.functor.map X.g =
    T.functor.map _ ≫ T.functor.map (S.functor.map
      (ShiftedDifferentialObject.Differential.previous S.functor X.d))
  erw [ShiftedDifferentialObject.Differential.map, ← T.functor.map_comp,
    ← T.functor.map_comp, ← Category.assoc,
    S.functor.asEquivalence.counitIso_inv_hom_id_app, Category.id_comp, T.functor.map_comp]

/-- The canonical connecting representative kills the translated map `f`. -/
theorem outerToHomology_zero (X : ShiftedExactCouple S T) :
    T.functor.map X.f ≫ outerToHomology X = 0 := by
  dsimp only [outerToHomology, ShortComplex.liftToHomology]
  rw [← Category.assoc, ← Category.assoc, ShortComplex.comp_liftCycles]
  rw [ShortComplex.liftCycles_homologyπ_eq_zero_of_boundary _ _ _
    (map_f_map_g_boundary X), zero_comp]

/-- Canonical maps and descent side conditions for the derived shifted exact couple. -/
@[stacks 0AMJ "canonical derived shifted exact-couple data"]
noncomputable def data (X : ShiftedExactCouple S T) : Data X where
  fCycles := cyclesToOuter X
  fCycles_zero := by
    apply (cancel_mono (image.ι X.tAlpha)).1
    rw [Category.assoc, cyclesToOuter_comp_ι, ← Category.assoc,
      X.page.shortComplex.toCycles_i, zero_comp]
    exact previous_comp_f X
  gFromOuter := outerToHomology X
  map_f_gFromOuter_zero := outerToHomology_zero X

/-- The canonical induced maps form the derived shifted exact couple. -/
@[stacks 0AMJ "canonical derived shifted exact-couple laws"]
theorem laws (X : ShiftedExactCouple S T) : Laws (data X) := sorry

/-- A coherent source of derived shifted-couple data for every first shift with fixed second
shift `T`. -/
@[stacks 0AMJ "iterable derived shifted exact-couple construction"]
structure Construction (T : C ≌ C) where
  /-- Concrete data for one derivation step. -/
  data : {S : C ≌ C} → (X : ShiftedExactCouple S T) → Data X
  /-- Proposition-valued certification of the data for one derivation step. -/
  laws : {S : C ≌ C} → (X : ShiftedExactCouple S T) → Laws (data X)

/-- Canonical derivation for every first shift, with the second shift fixed. -/
@[stacks 0AMJ "canonical derived shifted exact-couple construction"]
noncomputable def construction (T : C ≌ C) : Construction T where
  data := data
  laws := laws

namespace Construction

/-- Derive a shifted exact couple using the data selected by a coherent construction. -/
@[stacks 0AMJ "derived shifted exact couple"]
noncomputable def derived (K : Construction T) (X : ShiftedExactCouple S T) :
    ShiftedExactCouple (S.trans T) T :=
  ofData (K.data X) (K.laws X)

/-- Iterate a coherent derived shifted-exact-couple construction. -/
@[stacks 0AMJ "iterated derived shifted couple"]
noncomputable def iterate (K : Construction T) (X : ShiftedExactCouple S T) :
    (n : ℕ) → ShiftedExactCouple (ShiftedSpectralSequence.pageShift S T ⟨n + 1, Nat.succ_pos _⟩) T
  | 0 => X
  | n + 1 => K.derived (K.iterate X n)

namespace Iteration

/-- The zeroth iteration is the input shifted exact couple. -/
@[simp]
theorem zero (K : Construction T) (X : ShiftedExactCouple S T) : K.iterate X 0 = X := sorry

/-- The page object of the zeroth iteration is the input page object. -/
@[simp]
theorem zero_E (K : Construction T) (X : ShiftedExactCouple S T) :
    (K.iterate X 0).E = X.E := sorry

/-- The differential of the zeroth iteration is the input page differential. -/
@[simp]
theorem zero_d (K : Construction T) (X : ShiftedExactCouple S T) :
    (K.iterate X 0).d = X.d := sorry

/-- The successor iteration derives the preceding shifted exact couple. -/
@[simp]
theorem succ (K : Construction T) (X : ShiftedExactCouple S T) (n : ℕ) :
    K.iterate X (n + 1) = K.derived (K.iterate X n) := sorry

end Iteration

/-- The shifted spectral sequence associated to a coherently iterable derived shifted-exact-couple
construction. -/
@[stacks 0AMJ "associated shifted spectral sequence"]
noncomputable def associatedSpectralSequence
    (K : Construction T) (X : ShiftedExactCouple S T) :
    ShiftedSpectralSequence (ShiftedSpectralSequence.pageShift S T) :=
  { page := fun
      | ⟨n + 1, _⟩ => (K.data (K.iterate X n)).page
    iso := fun
      | ⟨n + 1, _⟩ => Iso.refl (K.iterate X (n + 1)).E }

end Construction

/-- The canonical derived shifted exact couple. -/
noncomputable abbrev derived (X : ShiftedExactCouple S T) :
    ShiftedExactCouple (S.trans T) T :=
  (construction T).derived X

/-- Iteration of the canonical derived shifted exact couple. -/
noncomputable abbrev iterate (X : ShiftedExactCouple S T) :
    (n : ℕ) → ShiftedExactCouple (ShiftedSpectralSequence.pageShift S T ⟨n + 1, Nat.succ_pos _⟩) T :=
  (construction T).iterate X

/-- The spectral sequence canonically associated to a shifted exact couple. -/
@[stacks 0AMJ "canonical associated shifted spectral sequence"]
noncomputable abbrev associatedSpectralSequence (X : ShiftedExactCouple S T) :
    ShiftedSpectralSequence (ShiftedSpectralSequence.pageShift S T) :=
  (construction T).associatedSpectralSequence X

namespace Page

/-- Page `r + 1` is the page-one shifted differential object of the `r`-fold iterate. -/
@[stacks 0AMJ "associated shifted page complex"]
theorem complex (X : ShiftedExactCouple S T) (r : ℕ) :
    (associatedSpectralSequence X).page ⟨r + 1, Nat.succ_pos _⟩ =
      (data (iterate X r)).page := sorry

/-- The object on page `r + 1` is the page object of the `r`-fold iterate. -/
@[stacks 0AMJ "associated shifted page object"]
theorem obj (X : ShiftedExactCouple S T) (r : ℕ) :
    ((associatedSpectralSequence X).page ⟨r + 1, Nat.succ_pos _⟩).obj =
      (iterate X r).E := sorry

/-- The differential on page `r + 1` is the page-one differential of the `r`-fold shifted
derived couple. -/
@[stacks 0AMJ "associated shifted page differential"]
theorem differential (X : ShiftedExactCouple S T) (r : ℕ) :
    ((associatedSpectralSequence X).page ⟨r + 1, Nat.succ_pos _⟩).d =
      (iterate X r).d := sorry

end Page

end Derived

end ShiftedExactCouple

end Derived

end CategoryTheory
