module

public import ReasLib.Algebra.Homology.SpectralSequence.Grothendieck.Functor
public import ReasLib.Algebra.Homology.SpectralSequence.Grothendieck.Map.Total.Forget

/-!
# Page-Two Comparison for Total Grothendieck Spectral Sequences

This leaf exposes the second-page entry carried by a total realization and its natural
comparison with the corresponding derived-base functor.
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

/-- The `(p, q)` entry on the second page, functorial in a total Grothendieck
spectral-sequence realization. -/
@[stacks 015N "page-two source functor on total Grothendieck spectral sequences"]
noncomputable def pageTwoSource
    (G : B ⥤ C) [G.Additive] (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C) (p : ℕ) (q : ℤ) :
    Total G RF RGF ⥤ C :=
  forgetSequence ⋙ CategoryTheory.SpectralSequence.pageFunctor C _ 0 2 ⋙
    HomologicalComplex.eval C _ (Int.ofNat p, q)

/-- Evaluation of `pageTwoSource` returns the selected entry of the realization's
second page. -/
@[simp, stacks 015N "page-two source functor on total Grothendieck spectral sequences"]
theorem pageTwoSource_obj
    (G : B ⥤ C) [G.Additive] (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C) (p : ℕ) (q : ℤ)
    (S : Total G RF RGF) :
    (pageTwoSource G RF RGF p q).obj S =
      (S.realization.sequence.page 2).X (Int.ofNat p, q) := sorry

/-- The morphism action of `pageTwoSource` is evaluation of the realization's
second-page map. -/
@[simp, stacks 015N "page-two source functor on total Grothendieck spectral sequences"]
theorem pageTwoSource_map
    (G : B ⥤ C) [G.Additive] (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C) (p : ℕ) (q : ℤ)
    {S T : Total G RF RGF} (f : S ⟶ T) :
    (pageTwoSource G RF RGF p q).map f =
      eqToHom (pageTwoSource_obj G RF RGF p q S) ≫
        (f.map.sequenceMap.hom 2).f (Int.ofNat p, q) ≫
        eqToHom (pageTwoSource_obj G RF RGF p q T).symm := sorry

/-- The canonical `(p, q)` comparison at a total object.

This component packages the dependent object equalities between the selected page entry and the
derived-base page functor.  Downstream statements can use this owner without repeating
`eqToIso` transports. -/
@[stacks 015N "page-two comparison component on total Grothendieck spectral sequences"]
noncomputable def pageTwoComparisonComponent
    (G : B ⥤ C) [G.Additive] (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C) (p : ℕ) (q : ℤ)
    (S : Total G RF RGF) :
    (pageTwoSource G RF RGF p q).obj S ≅
      (forgetBase ⋙ pageTwoFunctor G RF p q).obj S :=
  eqToIso (pageTwoSource_obj G RF RGF p q S) ≪≫
    S.realization.pageTwoIso p q ≪≫
    eqToIso (pageTwoFunctor_obj G RF p q S.base).symm

/-- Naturality of the page-two comparison across a total morphism. -/
@[reassoc, stacks 015N "naturality of the page-two comparison on total Grothendieck spectral sequences"]
theorem pageTwoComparison_naturality
    (G : B ⥤ C) [G.Additive] (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C) (p : ℕ) (q : ℤ)
    {S T : Total G RF RGF} (f : S ⟶ T) :
    (pageTwoSource G RF RGF p q).map f ≫
        (pageTwoComparisonComponent G RF RGF p q T).hom =
    (pageTwoComparisonComponent G RF RGF p q S).hom ≫
        ((forgetBase ⋙ pageTwoFunctor G RF p q).map f) := sorry

/-- Naturality of the inverse page-two comparison across a total morphism. -/
@[reassoc, stacks 015N "inverse naturality of the page-two comparison on total Grothendieck spectral sequences"]
theorem pageTwoComparison_inv_naturality
    (G : B ⥤ C) [G.Additive] (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C) (p : ℕ) (q : ℤ)
    {S T : Total G RF RGF} (f : S ⟶ T) :
    ((forgetBase ⋙ pageTwoFunctor G RF p q).map f) ≫
        (pageTwoComparisonComponent G RF RGF p q T).inv =
      (pageTwoComparisonComponent G RF RGF p q S).inv ≫
        (pageTwoSource G RF RGF p q).map f := sorry

/-- The page-two comparison, natural in the total Grothendieck spectral-sequence realization. -/
@[stacks 015N "page-two comparison on total Grothendieck spectral sequences"]
noncomputable def pageTwoComparison
    (G : B ⥤ C) [G.Additive] (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C) (p : ℕ) (q : ℤ) :
  pageTwoSource G RF RGF p q ≅ forgetBase ⋙ pageTwoFunctor G RF p q :=
  NatIso.ofComponents (fun S ↦ pageTwoComparisonComponent G RF RGF p q S)
    (fun f ↦ pageTwoComparison_naturality G RF RGF p q f)

/-- The forward component of `pageTwoComparison` is the comparison stored in the
realization. -/
@[simp, stacks 015N "page-two comparison on total Grothendieck spectral sequences"]
theorem pageTwoComparison_hom_app
    (G : B ⥤ C) [G.Additive] (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C) (p : ℕ) (q : ℤ)
    (S : Total G RF RGF) :
    (pageTwoComparison G RF RGF p q).hom.app S =
      (pageTwoComparisonComponent G RF RGF p q S).hom := sorry

/-- The inverse component of `pageTwoComparison` is the inverse comparison stored in the
realization. -/
@[simp, stacks 015N "page-two comparison on total Grothendieck spectral sequences"]
theorem pageTwoComparison_inv_app
    (G : B ⥤ C) [G.Additive] (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C) (p : ℕ) (q : ℤ)
    (S : Total G RF RGF) :
    (pageTwoComparison G RF RGF p q).inv.app S =
      (pageTwoComparisonComponent G RF RGF p q S).inv := sorry

/-- The complete page-two comparison component is the isomorphism stored by the realization. -/
@[simp, stacks 015N "page-two comparison component on total Grothendieck spectral sequences"]
theorem pageTwoComparison_app
    (G : B ⥤ C) [G.Additive] (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C) (p : ℕ) (q : ℤ)
    (S : Total G RF RGF) :
    (pageTwoComparison G RF RGF p q).app S =
      pageTwoComparisonComponent G RF RGF p q S := sorry

/-- The forward map of the canonical page-two comparison component. -/
@[simp, stacks 015N "forward page-two comparison component"]
theorem pageTwoComparisonComponent_hom
    (G : B ⥤ C) [G.Additive] (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C) (p : ℕ) (q : ℤ)
    (S : Total G RF RGF) :
    (pageTwoComparisonComponent G RF RGF p q S).hom =
      eqToHom (pageTwoSource_obj G RF RGF p q S) ≫
        (S.realization.pageTwoIso p q).hom ≫
        eqToHom (pageTwoFunctor_obj G RF p q S.base).symm := sorry

/-- The inverse map of the canonical page-two comparison component. -/
@[simp, stacks 015N "inverse page-two comparison component"]
theorem pageTwoComparisonComponent_inv
    (G : B ⥤ C) [G.Additive] (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C) (p : ℕ) (q : ℤ)
    (S : Total G RF RGF) :
    (pageTwoComparisonComponent G RF RGF p q S).inv =
      eqToHom (pageTwoFunctor_obj G RF p q S.base) ≫
        (S.realization.pageTwoIso p q).inv ≫
        eqToHom (pageTwoSource_obj G RF RGF p q S).symm := sorry

/-- Conjugating a target page-two map by the comparison recovers the source map. -/
@[reassoc, stacks 015N "source-map computation for the total Grothendieck page two"]
theorem pageTwoComparison_source_map
    (G : B ⥤ C) [G.Additive] (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C) (p : ℕ) (q : ℤ)
    {S T : Total G RF RGF} (f : S ⟶ T) :
    (pageTwoComparison G RF RGF p q).hom.app S ≫
        ((forgetBase ⋙ pageTwoFunctor G RF p q).map f) ≫
        (pageTwoComparison G RF RGF p q).inv.app T =
      (pageTwoSource G RF RGF p q).map f := sorry

/-- Conjugating a source page-two map by the inverse comparison recovers the target map. -/
@[reassoc, stacks 015N "target-map computation for the total Grothendieck page two"]
theorem pageTwoComparison_target_map
    (G : B ⥤ C) [G.Additive] (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C) (p : ℕ) (q : ℤ)
    {S T : Total G RF RGF} (f : S ⟶ T) :
    (pageTwoComparison G RF RGF p q).inv.app S ≫
        (pageTwoSource G RF RGF p q).map f ≫
        (pageTwoComparison G RF RGF p q).hom.app T =
      ((forgetBase ⋙ pageTwoFunctor G RF p q).map f) := sorry

/- Axiom audit: the source functor has explicit object and morphism data.  The comparison uses
the realization's explicit component isomorphism; `sorryAx` is confined to naturality and
component-computation propositions. -/

end CategoryTheory.Functor.RightDerived.Grothendieck.SpectralSequence.Total
