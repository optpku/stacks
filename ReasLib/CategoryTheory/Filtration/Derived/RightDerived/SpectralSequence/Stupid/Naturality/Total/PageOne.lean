/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Stupid.Naturality.Total
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Stupid.Naturality.Comparison
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Realization.Total.PageOne

/-!
# First page on total stupid-filtration realizations

The source reuses the neutral page-entry functor, while the target evaluates the source cochain
complex in degree `p` and applies the degree-`q` right-derived functor.  The stored first-page
isomorphisms assemble into a natural isomorphism between these functors.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid.Realization.Total

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]

/-- The `(p, q)` entry of the first page, functorial on total stupid-filtration realizations. -/
@[stacks 0FLK "first-page source functor on total stupid realizations"]
noncomputable abbrev pageOneSource (p : ℤ) (q : ℕ) :
    Realization.Total F ⥤ B :=
  genericFunctor F ⋙
    RightDerived.SpectralSequence.Realization.Total.pageOneSource F p (Int.ofNat q)

/-- The degree-`q` right-derived image of the degree-`p` source term. -/
@[stacks 0FLK "first-page target functor on total stupid realizations"]
noncomputable abbrev pageOneTarget (p : ℤ) (q : ℕ) :
    Realization.Total F ⥤ B :=
  forgetBase F ⋙ HomologicalComplex.eval A (up ℤ) p ⋙ F.rightDerived q

/-- Naturality of the stored first-page comparisons on total stupid realizations. -/
@[stacks 0FLK "naturality for total stupid first-page comparisons"]
theorem pageOneComparison_naturality (p : ℤ) (q : ℕ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (pageOneSource F p q).map m ≫ (T.obj.pageOneIso p q).hom =
      (S.obj.pageOneIso p q).hom ≫ (pageOneTarget F p q).map m := sorry

/-- The first-page comparison, natural in a total stupid-filtration realization. -/
@[stacks 0FLK "first-page comparison on total stupid realizations"]
noncomputable def pageOneComparison (p : ℤ) (q : ℕ) :
    pageOneSource F p q ≅ pageOneTarget F p q :=
  NatIso.ofComponents (fun S => S.obj.pageOneIso p q)
    (fun m => pageOneComparison_naturality F p q m)

/-- The first-page source evaluates to the selected page entry. -/
@[simp, stacks 0FLK "first-page source object on total stupid realizations"]
theorem pageOneSource_obj (p : ℤ) (q : ℕ) (S : Realization.Total F) :
    (pageOneSource F p q).obj S =
      (S.obj.sequence.page 1).X (p, Int.ofNat q) := sorry

/-- The first-page source maps by the selected page component. -/
@[simp, stacks 0FLK "first-page source map on total stupid realizations"]
theorem pageOneSource_map (p : ℤ) (q : ℕ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (pageOneSource F p q).map m =
      (m.displayed.sequenceMap.hom 1 zero_le_one).f (p, Int.ofNat q) := sorry

/-- The first-page target evaluates to the degree-`q` right-derived image of the source term. -/
@[simp, stacks 0FLK "first-page target object on total stupid realizations"]
theorem pageOneTarget_obj (p : ℤ) (q : ℕ) (S : Realization.Total F) :
    (pageOneTarget F p q).obj S = (F.rightDerived q).obj (S.base.X p) := sorry

/-- The first-page target maps by applying the degree-`q` right-derived functor termwise. -/
@[simp, stacks 0FLK "first-page target map on total stupid realizations"]
theorem pageOneTarget_map (p : ℤ) (q : ℕ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (pageOneTarget F p q).map m = (F.rightDerived q).map (m.base.f p) := sorry

/-- A first-page comparison component is the isomorphism stored by the realization. -/
@[simp, stacks 0FLK "first-page comparison component on total stupid realizations"]
theorem pageOneComparison_app (p : ℤ) (q : ℕ) (S : Realization.Total F) :
    (pageOneComparison F p q).app S = S.obj.pageOneIso p q := sorry

/-- The forward first-page component is the stored comparison morphism. -/
@[simp, stacks 0FLK "forward first-page comparison component on total stupid realizations"]
theorem pageOneComparison_hom_app (p : ℤ) (q : ℕ) (S : Realization.Total F) :
    (pageOneComparison F p q).hom.app S = (S.obj.pageOneIso p q).hom := sorry

/-- The inverse first-page component is the inverse stored comparison morphism. -/
@[simp, stacks 0FLK "inverse first-page comparison component on total stupid realizations"]
theorem pageOneComparison_inv_app (p : ℤ) (q : ℕ) (S : Realization.Total F) :
    (pageOneComparison F p q).inv.app S = (S.obj.pageOneIso p q).inv := sorry

/-- Naturality of the forward total first-page comparison. -/
@[reassoc, stacks 0FLK "forward naturality of the total stupid first-page comparison"]
theorem pageOneComparison_hom_naturality (p : ℤ) (q : ℕ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (pageOneSource F p q).map m ≫ (pageOneComparison F p q).hom.app T =
      (pageOneComparison F p q).hom.app S ≫ (pageOneTarget F p q).map m := sorry

/-- Naturality of the inverse total first-page comparison. -/
@[reassoc, stacks 0FLK "inverse naturality of the total stupid first-page comparison"]
theorem pageOneComparison_inv_naturality (p : ℤ) (q : ℕ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (pageOneTarget F p q).map m ≫ (pageOneComparison F p q).inv.app T =
      (pageOneComparison F p q).inv.app S ≫ (pageOneSource F p q).map m := sorry

/-- Compute a source page map by conjugating the target map through the comparison. -/
@[reassoc, stacks 0FLK "source map through the total stupid first-page comparison"]
theorem pageOneComparison_source_map (p : ℤ) (q : ℕ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (pageOneComparison F p q).hom.app S ≫ (pageOneTarget F p q).map m ≫
        (pageOneComparison F p q).inv.app T =
      (pageOneSource F p q).map m := sorry

/-- Compute a target page map by conjugating the source map through the inverse comparison. -/
@[reassoc, stacks 0FLK "target map through the total stupid first-page comparison"]
theorem pageOneComparison_target_map (p : ℤ) (q : ℕ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (pageOneComparison F p q).inv.app S ≫ (pageOneSource F p q).map m ≫
        (pageOneComparison F p q).hom.app T =
      (pageOneTarget F p q).map m := sorry

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid.Realization.Total
