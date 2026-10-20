module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.Leray
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.Leray.Linear
public import ReasLib.AlgebraicGeometry.RingedSpace.PushforwardStructure
public import ReasLib.CategoryTheory.Homology.SpectralSequence.ChangeOfCategory
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Source-scalar structure on the Leray spectral sequence

Replacing `f : X ⟶ Y` by `X ⟶ (Y, f_* 𝒪_X)` produces a Leray spectral sequence valued in
modules over the global section ring of the pushed-forward structure sheaf.  This ring is
canonically isomorphic to `Γ(X, 𝒪_X)`.  A comparison package records that forgetting this module
structure recovers the ordinary additive Leray sequence from the second page onward.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleLeray.SourceScalars

variable {X Y : RingedSpace.{u}}

/-- The global section ring of the pushed-forward structure sheaf. -/
@[stacks 01F3 "source scalar ring for Leray"]
abbrev ring (f : X ⟶ Y) : CommRingCat.{u} :=
  RingedSpace.globalSectionsRing (RingedSpace.Hom.PushforwardStructure.target f)

/-- The forgetful functor from modules over the source scalar ring to additive groups. -/
@[stacks 01F3 "forgetting source scalars"]
abbrev forget (f : X ⟶ Y) : ModuleCat (ring f) ⥤ AddCommGrpCat.{u} :=
  forget₂ (ModuleCat (ring f)) AddCommGrpCat.{u}

/-- The source-linear Leray realization obtained from
`X ⟶ (Y, f_* 𝒪_X)`. -/
@[stacks 01F3 "source-linear Leray realization"]
abbrev Realization (f : X ⟶ Y) (K : DerivedCategory.Plus X.Modules) :=
  ModuleLeray.Linear.Realization (RingedSpace.Hom.PushforwardStructure.lift f) K

/-- The underlying additive spectral sequence of a source-linear Leray realization. -/
@[stacks 01F3 "underlying source-linear Leray spectral sequence"]
noncomputable abbrev underlyingSequence {f : X ⟶ Y}
    {K : DerivedCategory.Plus X.Modules} (S : Realization f K) :
    CohomologicalSpectralSequence AddCommGrpCat.{u} 0 :=
  SpectralSequence.mapCategory (forget f) S.sequence

/-- A source-linear Leray realization together with an additive Leray realization and a comparison
that is an isomorphism from the second page onward. -/
@[stacks 01F3 "source-scalar structure on Leray"]
structure Comparison (f : X ⟶ Y) (K : DerivedCategory.Plus X.Modules) where
  /-- The Leray realization retaining the source scalar action. -/
  linear : Realization f K
  /-- The ordinary additive Leray realization. -/
  additive : ModuleLeray.Realization f K
  /-- The comparison after forgetting the source scalar action. -/
  hom : underlyingSequence linear ⟶ additive.sequence
  /-- The comparison is invertible on every page from `E₂` onward. -/
  isIsoFromTwo : hom.IsIsoFrom 2 (Int.natCast_nonneg 2)

/-- The source scalar ring is canonically isomorphic to `Γ(X, 𝒪_X)`. -/
@[stacks 01F3 "source scalar ring identification"]
theorem ring_isIsomorphic (f : X ⟶ Y) :
    IsIsomorphic (ring f) (RingedSpace.globalSectionsRing X) := sorry

/-- Remark 20.13.5, generalized to bounded-below derived modules: the Leray spectral sequence
admits a source-scalar lift whose underlying additive sequence agrees from `E₂` onward. -/
@[stacks 01F3 "source-scalar Leray existence"]
theorem nonempty (f : X ⟶ Y) (K : DerivedCategory.Plus X.Modules) :
    Nonempty (Comparison f K) := sorry

/-- Remark 20.13.5 for an ordinary module sheaf. -/
@[stacks 01F3]
theorem ofModule (f : X ⟶ Y) (F : X.Modules) :
    Nonempty (Comparison f ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj F)) := sorry

/-- Every entry on every page from `E₂` onward is isomorphic after forgetting source scalars. -/
@[stacks 01F3 "source-scalar Leray page comparison"]
theorem page_isIsomorphic {f : X ⟶ Y} {K : DerivedCategory.Plus X.Modules}
    (C : Comparison f K) (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) :
    IsIsomorphic
      (((underlyingSequence C.linear).page r ((Int.natCast_nonneg 2).trans hr)).X pq)
      ((C.additive.sequence.page r ((Int.natCast_nonneg 2).trans hr)).X pq) := sorry

end AlgebraicGeometry.RingedSpace.ModuleLeray.SourceScalars
