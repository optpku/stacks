/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Preadditive.CompactObject
public import ReasLib.CategoryTheory.Pretriangulated.Generation.Localizing
public import ReasLib.CategoryTheory.Functor.FullyFaithful
public import ReasLib.CategoryTheory.Shift.ShiftedHom.Functor
public import Mathlib.CategoryTheory.Shift.ShiftedHom
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Full Faithfulness Detected on Compact Generators

The criteria in this module separate the ingredients of the standard derived-category
devissage argument.  Shifted Hom bijectivity is tested on compact generators, while detection
of isomorphisms and localizing generation are independent explicit hypotheses.
-/

open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

universe w vC uC vD uD

namespace CategoryTheory.Functor

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable [HasShift C ℤ] [HasShift D ℤ]

/-- A functor is fully faithful on all shifted Homs between a family of objects when its
canonical `ShiftedHom.map` is bijective for every pair in the family and every integer shift. -/
@[stacks 09R9 "shifted Hom bijectivity on generators"]
def IsFullyFaithfulOnShifts {I : Type w} (F : C ⥤ D) [F.CommShift ℤ]
    (E : I → C) : Prop :=
  ∀ (i j : I) (n : ℤ),
    Function.Bijective
      (fun f : E i ⟶ (shiftFunctor C n).obj (E j) ↦ ShiftedHom.map f F)

/-- A functor preserves every self-Ext group of an object when its canonical map on each
integer-shifted self Hom is bijective. -/
@[stacks 09R9 "self-Ext bijectivity"]
def IsFullyFaithfulOnSelfShifts (F : C ⥤ D) [F.CommShift ℤ] (E : C) : Prop :=
  ∀ n : ℤ,
    Function.Bijective
      (fun f : E ⟶ (shiftFunctor C n).obj E ↦ ShiftedHom.map f F)

/-- Full faithfulness on all shifted self-Homs is unchanged after identifying the image of the
object with a chosen target object. -/
@[stacks 09R9 "self-shift full faithfulness under an endpoint isomorphism"]
theorem isFullyFaithfulOnSelfShifts_iff_of_iso
    (F : C ⥤ D) [F.CommShift ℤ] {X : C} {Y : D} (h : F.obj X ≅ Y) :
    F.IsFullyFaithfulOnSelfShifts X ↔
      ∀ n : ℤ, Function.Bijective (F.shiftedHomMap h h n) := sorry

/-- The smallness bounds needed by the compact-generator full-faithfulness criterion.

This bundles the universe bookkeeping that is orthogonal to the mathematical hypotheses.  The
raw `UnivLE` parameters remain available on the low-level criteria below, while downstream
applications can depend on this single named owner. -/
@[stacks 09R9 "universe bounds for compact-generator full faithfulness"]
class CompactGeneratorBounds (C : Type uC) (D : Type uD)
    [Category.{vC} C] [Category.{vD} D] : Prop where
  source : UnivLE.{max uC vC, vC}
  target : UnivLE.{max uC vC, vD}

/-- Construct compact-generator bounds from the underlying universe inequalities. -/
@[stacks 09R9 "compact-generator universe-bound constructor"]
instance compactGeneratorBounds_of_univLE
    [UnivLE.{max uC vC, vC}] [UnivLE.{max uC vC, vD}] :
    CompactGeneratorBounds C D :=
  ⟨inferInstance, inferInstance⟩

namespace FullyFaithful

variable [HasZeroObject C] [HasZeroObject D]
variable [Preadditive C] [Preadditive D]
variable [UnivLE.{max uC vC, vC}] [UnivLE.{max uC vC, vD}]
variable [∀ n : ℤ, (shiftFunctor C n).Additive]
variable [∀ n : ℤ, (shiftFunctor D n).Additive]
variable [Pretriangulated C] [Pretriangulated D]
variable {F : C ⥤ D} {G : D ⥤ C} [F.CommShift ℤ] [F.IsTriangulated]

/-- A left adjoint induces bijections on every Hom set when it is fully faithful on a compact
family whose shifts detect isomorphisms and which localizing-generates the source, provided the
images of the family are compact as well.  The `UnivLE` assumptions align the coproduct universe
used by localizing generation with the two Hom universes.  No ambient coproduct-existence
assumption is needed: localizing generation and compactness are both formulated relative to
coproducts that exist. -/
@[stacks 09R9 "compact-family full-faithfulness criterion"]
theorem map_bijective_ofCompactGenerators {I : Type w} (adj : F ⊣ G) (E : I → C)
    (h_localizing : (ofObj E).IsLocalizingGenerator)
    (h_detecting : ((ofObj E).shiftClosure ℤ).IsDetecting)
    (h_source_compact : ∀ i, IsCompactObject (E i))
    (h_target_compact : ∀ i, IsCompactObject (F.obj (E i)))
    (h_ext : F.IsFullyFaithfulOnShifts E) :
    ∀ X Y : C, Function.Bijective
      (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) := sorry

/-- A compact family whose shifts detect isomorphisms and localizing-generate the source
produces a concrete fully faithful structure once shifted Homs on the family are preserved. -/
@[stacks 09R9 "fully faithful functor from compact generators"]
noncomputable def ofCompactGenerators {I : Type w} (adj : F ⊣ G) (E : I → C)
    (h_localizing : (ofObj E).IsLocalizingGenerator)
    (h_detecting : ((ofObj E).shiftClosure ℤ).IsDetecting)
    (h_source_compact : ∀ i, IsCompactObject (E i))
    (h_target_compact : ∀ i, IsCompactObject (F.obj (E i)))
    (h_ext : F.IsFullyFaithfulOnShifts E) : F.FullyFaithful :=
  ofMapBijective
    (map_bijective_ofCompactGenerators (C := C) (D := D) (F := F) (G := G)
      adj E h_localizing h_detecting
      h_source_compact h_target_compact h_ext)

/-- A concrete fully faithful functor from a compact family with explicit universe bounds. -/
@[stacks 09R9 "fully faithful functor from compact generators with explicit bounds"]
noncomputable def ofCompactGenerators_withBounds
    (h_bounds : CompactGeneratorBounds C D) {I : Type w} (adj : F ⊣ G) (E : I → C)
    (h_localizing : (ofObj E).IsLocalizingGenerator)
    (h_detecting : ((ofObj E).shiftClosure ℤ).IsDetecting)
    (h_source_compact : ∀ i, IsCompactObject (E i))
    (h_target_compact : ∀ i, IsCompactObject (F.obj (E i)))
    (h_ext : F.IsFullyFaithfulOnShifts E) : F.FullyFaithful :=
  @ofCompactGenerators C D _ _ _ _ _ _ _ _ h_bounds.source h_bounds.target
    _ _ _ _ F G _ _ I adj E h_localizing h_detecting
    h_source_compact h_target_compact h_ext

/-- The one-object compact-generator criterion: bijectivity on every shifted self Hom implies
full faithfulness once the shifts detect isomorphisms and the object localizing-generates the
source.  Source and image compactness are explicit because they are what makes the Hom tests
compatible with arbitrary coproducts. -/
@[stacks 09R9 "compact generator full-faithfulness criterion"]
theorem map_bijective_ofCompactGenerator (adj : F ⊣ G) (E : C)
    (h_localizing : (singleton E).IsLocalizingGenerator)
    (h_detecting : ((singleton E).shiftClosure ℤ).IsDetecting)
    (h_source_compact : IsCompactObject E)
    (h_target_compact : IsCompactObject (F.obj E))
    (h_ext : F.IsFullyFaithfulOnSelfShifts E) :
    ∀ X Y : C, Function.Bijective
      (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) := sorry

/-- The one-object compact-generator criterion, bundled as a concrete fully faithful
structure for direct downstream use. -/
@[stacks 09R9 "fully faithful functor from a compact generator"]
noncomputable def ofCompactGenerator (adj : F ⊣ G) (E : C)
    (h_localizing : (singleton E).IsLocalizingGenerator)
    (h_detecting : ((singleton E).shiftClosure ℤ).IsDetecting)
    (h_source_compact : IsCompactObject E)
    (h_target_compact : IsCompactObject (F.obj E))
    (h_ext : F.IsFullyFaithfulOnSelfShifts E) : F.FullyFaithful :=
  ofMapBijective
    (map_bijective_ofCompactGenerator (C := C) (D := D) (F := F) (G := G)
      adj E h_localizing h_detecting
      h_source_compact h_target_compact h_ext)

/-- A concrete fully faithful functor from one compact generator with explicit universe bounds. -/
@[stacks 09R9 "fully faithful functor from a compact generator with explicit bounds"]
noncomputable def ofCompactGenerator_withBounds
    (h_bounds : CompactGeneratorBounds C D) (adj : F ⊣ G) (E : C)
    (h_localizing : (singleton E).IsLocalizingGenerator)
    (h_detecting : ((singleton E).shiftClosure ℤ).IsDetecting)
    (h_source_compact : IsCompactObject E)
    (h_target_compact : IsCompactObject (F.obj E))
    (h_ext : F.IsFullyFaithfulOnSelfShifts E) : F.FullyFaithful :=
  @ofCompactGenerator C D _ _ _ _ _ _ _ _ h_bounds.source h_bounds.target
    _ _ _ _ F G _ _ adj E h_localizing h_detecting
    h_source_compact h_target_compact h_ext

end FullyFaithful

namespace FullyFaithful

variable [HasZeroObject C] [HasZeroObject D]
variable [Preadditive C] [Preadditive D]
variable [∀ n : ℤ, (shiftFunctor C n).Additive]
variable [∀ n : ℤ, (shiftFunctor D n).Additive]
variable [Pretriangulated C] [Pretriangulated D]
variable {F : C ⥤ D} {G : D ⥤ C} [F.CommShift ℤ] [F.IsTriangulated]

/-- The compact-family full-faithfulness criterion with the universe bounds supplied explicitly.

This bridge is useful when the category universe is not recoverable from an object term.  It keeps
the two genuinely required `UnivLE` witnesses visible without installing temporary instances. -/
@[stacks 09R9 "compact-family full-faithfulness with explicit universe bounds"]
theorem map_bijective_ofCompactGenerators_withBounds
    (h_bounds : CompactGeneratorBounds C D) {I : Type w} (adj : F ⊣ G) (E : I → C)
    (h_localizing : (ofObj E).IsLocalizingGenerator)
    (h_detecting : ((ofObj E).shiftClosure ℤ).IsDetecting)
    (h_source_compact : ∀ i, IsCompactObject (E i))
    (h_target_compact : ∀ i, IsCompactObject (F.obj (E i)))
    (h_ext : F.IsFullyFaithfulOnShifts E) :
    ∀ X Y : C, Function.Bijective
      (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) := sorry

/-- The one-object compact-generator criterion with explicit universe bounds. -/
@[stacks 09R9 "compact-generator criterion with explicit universe bounds"]
theorem map_bijective_ofCompactGenerator_withBounds
    (h_bounds : CompactGeneratorBounds C D) (adj : F ⊣ G) (E : C)
    (h_localizing : (singleton E).IsLocalizingGenerator)
    (h_detecting : ((singleton E).shiftClosure ℤ).IsDetecting)
    (h_source_compact : IsCompactObject E)
    (h_target_compact : IsCompactObject (F.obj E))
    (h_ext : F.IsFullyFaithfulOnSelfShifts E) :
    ∀ X Y : C, Function.Bijective
      (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) := sorry

/-- The compact-family criterion with universe bookkeeping supplied by a named bounds owner.

This is the family-level companion of `ofCompactGenerator_of_bounds`; its implementation passes
the bundled fields directly to the low-level construction and installs no local instances. -/
@[stacks 09R9 "compact-family full faithfulness with bundled universe bounds"]
noncomputable def ofCompactGenerators_of_bounds [h : CompactGeneratorBounds C D]
    {I : Type w} (adj : F ⊣ G) (E : I → C)
    (h_localizing : (ofObj E).IsLocalizingGenerator)
    (h_detecting : ((ofObj E).shiftClosure ℤ).IsDetecting)
    (h_source_compact : ∀ i, IsCompactObject (E i))
    (h_target_compact : ∀ i, IsCompactObject (F.obj (E i)))
    (h_ext : F.IsFullyFaithfulOnShifts E) : F.FullyFaithful :=
  @ofCompactGenerators C D _ _ _ _ _ _ _ _ h.source h.target
    _ _ _ _ F G _ _ I adj E h_localizing h_detecting
    h_source_compact h_target_compact h_ext

/-- The compact-generator criterion with universe bookkeeping supplied by a named bounds owner.

This is the preferred downstream entry point; `ofCompactGenerator` above remains the transparent
low-level form for developments that intentionally manage the two `UnivLE` instances directly.
The bundled fields are passed directly to the low-level declaration, so this bridge installs no
local instances. -/
@[stacks 09R9 "compact-generator full faithfulness with bundled universe bounds"]
noncomputable def ofCompactGenerator_of_bounds [h : CompactGeneratorBounds C D]
    (adj : F ⊣ G) (E : C)
    (h_localizing : (singleton E).IsLocalizingGenerator)
    (h_detecting : ((singleton E).shiftClosure ℤ).IsDetecting)
    (h_source_compact : IsCompactObject E)
    (h_target_compact : IsCompactObject (F.obj E))
    (h_ext : F.IsFullyFaithfulOnSelfShifts E) : F.FullyFaithful :=
  @ofCompactGenerator C D _ _ _ _ _ _ _ _ h.source h.target
    _ _ _ _ F G _ _ adj E h_localizing h_detecting
    h_source_compact h_target_compact h_ext

end FullyFaithful

end CategoryTheory.Functor
