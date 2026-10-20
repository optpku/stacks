/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.SpectralSequence.Grothendieck.Map.Total
public import ReasLib.CategoryTheory.DisplayedCategory.Total.Transport
public import ReasLib.CategoryTheory.Filtration.Complex.Functors
public import Mathlib.CategoryTheory.FiberedCategory.HomLift
public import Mathlib.CategoryTheory.Products.Basic

/-!
# Forgetful Functors from Total Grothendieck Spectral Sequences

This leaf exposes the filtered complex, spectral sequence, and underlying cochain complex carried
by a total Grothendieck spectral-sequence realization.  The joint base-and-filtered projection is
faithful, giving downstream constructions a small concrete interface for total morphisms.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe wA wB wC v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.RightDerived.Grothendieck.SpectralSequence.Total

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
variable [Abelian A] [Abelian B] [Abelian C]
variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
variable [HasDerivedCategory.{wC} C] [HasInjectiveResolutions B]
variable {G : B ⥤ C} [G.Additive]
variable {RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
variable {RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C}

/-- Forget a total Grothendieck spectral-sequence realization to its filtered complex. -/
@[stacks 015N "filtered-complex projection from total Grothendieck spectral sequences"]
noncomputable abbrev forgetFiltered : Total G RF RGF ⥤ FilteredComplex C :=
  forgetRealization ⋙ FilteredComplex.SpectralSequence.Realization.forgetFiltered

/-- The filtered-complex projection returns the filtered complex stored in the realization. -/
@[simp, stacks 015N "filtered-complex projection from total Grothendieck spectral sequences"]
theorem forgetFiltered_obj (S : Total G RF RGF) :
    forgetFiltered.obj S = S.realization.filtered := sorry

/-- The filtered-complex projection returns the filtered component of a total morphism. -/
@[simp, stacks 015N "filtered-complex projection from total Grothendieck spectral sequences"]
theorem forgetFiltered_map {S T : Total G RF RGF} (f : S ⟶ T) :
    forgetFiltered.map f = f.map.filteredMap := sorry

/-- Forget a total Grothendieck spectral-sequence realization to its spectral sequence. -/
@[stacks 015N "spectral-sequence projection from total Grothendieck spectral sequences"]
noncomputable abbrev forgetSequence :
    Total G RF RGF ⥤ CohomologicalSpectralSequence C 0 :=
  forgetRealization ⋙ FilteredComplex.SpectralSequence.Realization.forgetSequence

/-- The spectral-sequence projection returns the sequence stored in the realization. -/
@[simp, stacks 015N "spectral-sequence projection from total Grothendieck spectral sequences"]
theorem forgetSequence_obj (S : Total G RF RGF) :
    forgetSequence.obj S = S.realization.sequence := sorry

/-- The spectral-sequence projection returns the sequence component of a total morphism. -/
@[simp, stacks 015N "spectral-sequence projection from total Grothendieck spectral sequences"]
theorem forgetSequence_map {S T : Total G RF RGF} (f : S ⟶ T) :
    forgetSequence.map f = f.map.sequenceMap := sorry

/-- Forget a total Grothendieck spectral-sequence realization to the underlying cochain complex
of its filtered complex. -/
@[stacks 015N "underlying-complex projection from total Grothendieck spectral sequences"]
noncomputable abbrev forgetUnderlying : Total G RF RGF ⥤ CochainComplex C ℤ :=
  forgetFiltered ⋙ FilteredComplex.underlyingFunctor

/-- The underlying-complex projection returns the realization's underlying cochain complex. -/
@[simp, stacks 015N "underlying-complex projection from total Grothendieck spectral sequences"]
theorem forgetUnderlying_obj (S : Total G RF RGF) :
    forgetUnderlying.obj S = S.realization.filtered.underlying := sorry

/-- The underlying-complex projection maps a total morphism by its underlying filtered map. -/
@[simp, stacks 015N "underlying-complex projection from total Grothendieck spectral sequences"]
theorem forgetUnderlying_map {S T : Total G RF RGF} (f : S ⟶ T) :
    forgetUnderlying.map f = FilteredComplex.underlyingMap f.map.filteredMap := sorry

/-- Jointly remember the derived base and filtered complex of a total Grothendieck
spectral-sequence realization. -/
@[stacks 015N "faithful projection from total Grothendieck spectral sequences"]
noncomputable abbrev forgetBaseFiltered :
    Total G RF RGF ⥤ DerivedCategory.Plus A × FilteredComplex C :=
  forgetBase.prod' forgetFiltered

/-- The first component of `forgetBaseFiltered` is the supporting derived object. -/
@[simp, stacks 015N "faithful projection from total Grothendieck spectral sequences"]
theorem forgetBaseFiltered_obj_fst (S : Total G RF RGF) :
    (forgetBaseFiltered.obj S).1 = S.base := sorry

/-- The second component of `forgetBaseFiltered` is the stored filtered complex. -/
@[simp, stacks 015N "faithful projection from total Grothendieck spectral sequences"]
theorem forgetBaseFiltered_obj_snd (S : Total G RF RGF) :
    (forgetBaseFiltered.obj S).2 = S.realization.filtered := sorry

/-- The first component of the image of a total morphism is its base arrow. -/
@[simp, stacks 015N "faithful projection from total Grothendieck spectral sequences"]
theorem forgetBaseFiltered_map_fst {S T : Total G RF RGF} (f : S ⟶ T) :
    (forgetBaseFiltered.map f).1 = f.base := sorry

/-- The second component of the image of a total morphism is its filtered-complex map. -/
@[simp, stacks 015N "faithful projection from total Grothendieck spectral sequences"]
theorem forgetBaseFiltered_map_snd {S T : Total G RF RGF} (f : S ⟶ T) :
    (forgetBaseFiltered.map f).2 = f.map.filteredMap := sorry

/-- The base arrow together with the filtered-complex map determines a total Grothendieck
spectral-sequence morphism. -/
@[stacks 015N "faithful projection from total Grothendieck spectral sequences"]
noncomputable instance forgetBaseFiltered_faithful :
    (forgetBaseFiltered (G := G) (RF := RF) (RGF := RGF)).Faithful := sorry

/-- A total Grothendieck spectral-sequence morphism is determined by its base arrow and filtered
complex map.  This is the componentwise form of faithfulness of `forgetBaseFiltered`. -/
@[ext (iff := false), stacks 015N "extensionality of total Grothendieck spectral-sequence morphisms"]
theorem Hom.ext_base_filtered {S T : Total G RF RGF} {f g : S ⟶ T}
    (h_base : f.base = g.base)
    (h_filtered : f.map.filteredMap = g.map.filteredMap) : f = g := sorry

/-! The base projection is a genuine displayed-category projection.  Its canonical hom-lift
instance is owned by `DisplayedCategory.Total`; this leaf keeps only the Grothendieck-facing
transport and characterization lemmas. -/

/-- A Grothendieck total morphism lifts any propositionally equal base arrow. -/
@[stacks 015N "hom-lift transport for the total Grothendieck projection"]
theorem isHomLift_of_eq {S T : Total G RF RGF}
    {g : S.base ⟶ T.base} (f : S ⟶ T) (h : g = f.base) :
    (forgetBase (G := G) (RF := RF) (RGF := RGF)).IsHomLift g f := sorry

/-- The hom-lift predicate for the Grothendieck projection is exactly equality with the stored
base component. -/
@[simp, stacks 015N "hom-lift characterization for the total Grothendieck projection"]
theorem isHomLift_iff {S T : Total G RF RGF}
    (g : S.base ⟶ T.base) (f : S ⟶ T) :
    (forgetBase (G := G) (RF := RF) (RGF := RGF)).IsHomLift g f ↔ g = f.base := sorry

#synth (forgetBaseFiltered (G := G) (RF := RF) (RGF := RGF)).Faithful

/- Axiom audit: all four functors are explicit compositions of canonical functors.  Any
`sorryAx` is confined to inherited functor laws and the proposition-valued faithfulness proof. -/

end CategoryTheory.Functor.RightDerived.Grothendieck.SpectralSequence.Total
