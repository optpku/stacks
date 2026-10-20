module

public import ReasLib.CategoryTheory.Filtration.Complex.GradedPieceColumn
public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence.Presentation
public import ReasLib.CategoryTheory.Homology.SpectralSequence.PageZeroColumn

/-!
# Spectral Sequences Associated to Filtered Complexes

This file packages the zeroth-page comparison, the resulting first-page comparison, the
canonical identifications `E₀^{p,q} = grᵖ K^{p+q}` and `E₁^{p,q} = H^{p+q}(grᵖ K)` of the
explicit `Zᵣ/Bᵣ` representatives, and the association of a cohomological spectral sequence to a
filtered complex, whose initial-page comparisons are required to be these canonical ones.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredComplex

/-- A chosen comparison between the zeroth page of a spectral sequence and the reindexed
graded-piece complexes of a filtered complex. Each column is a complex in its own right, so the
columnwise form avoids imposing an artificial definitional realization of the full zeroth page. -/
@[stacks 012M "zeroth-page comparison with graded pieces"]
structure Page.Zero.Comparison (K : FilteredComplex C)
    (E : CohomologicalSpectralSequence C 0) where
  /-- The comparison of the column at filtration degree `p`. -/
  columnIso : ∀ p : ℤ, E.pageZeroColumn p ≅ GradedPiece.Column.complex K p

/-- The representation-independent proposition that the zeroth page of `E` is the graded-piece
complex of `K`. -/
@[stacks 012M "zeroth page is the graded-piece complex"]
def Page.Zero.IsGradedPiece (K : FilteredComplex C)
    (E : CohomologicalSpectralSequence C 0) : Prop :=
  Nonempty (Page.Zero.Comparison K E)

/-- A chosen zeroth-page comparison witnesses the corresponding representation-independent
property. -/
@[stacks 012M "zeroth-page comparison witnesses the graded-piece property"]
theorem Page.Zero.Comparison.isGradedPiece
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    (A : Page.Zero.Comparison K E) :
    Page.Zero.IsGradedPiece K E := sorry

/-- A zeroth-page comparison induces the usual identification of the first-page objects with
the cohomology of the graded-piece complexes. -/
@[stacks 012M "first-page comparison from a zeroth-page comparison"]
noncomputable def Page.One.iso
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    (A : Page.Zero.Comparison K E) (p q : ℤ) :
    (E.page 1).X (p, q) ≅ (K.gradedPiece p).homology (p + q) :=
  (E.iso 0 1 (p, q)).symm ≪≫
    (CohomologicalSpectralSequence.PageZeroColumn.homologyIso E p q).symm ≪≫
    HomologicalComplex.homologyMapIso (A.columnIso p) q ≪≫
    GradedPiece.Column.homologyIso K p q

/-! ## Canonical identifications of the initial explicit pages -/

/-- In filtration degree `p`, the whole stage `Fᵖ Kⁿ` lies in the zeroth cycle representative
`Z₀^p = (Fᵖ Kⁿ ∩ d⁻¹(Fᵖ Kⁿ⁺¹)) + Fᵖ⁺¹ Kⁿ`, because the differential preserves the filtration. -/
@[stacks 012M "the zeroth cycle representative is the whole stage"]
theorem Page.Zero.stage_le_cycle (K : FilteredComplex C) (n p : ℤ) :
    (K.X n).filtration.stage p ≤ Page.Representative.cycle K 0 n p := sorry

/-- The stage `Fᵖ Kⁿ` mapped to the zeroth explicit page kills `Fᵖ⁺¹ Kⁿ`, which is contained in
the zeroth boundary representative. -/
@[stacks 012M "the next stage vanishes on the zeroth page"]
theorem Page.Zero.succInclusion_comp_eq_zero (K : FilteredComplex C) (n p : ℤ) :
    (K.X n).filtration.succInclusion p ≫
        Subobject.ofLE ((K.X n).filtration.stage p) (Page.Representative.cycle K 0 n p)
          (Page.Zero.stage_le_cycle K n p) ≫
        Page.Representative.toQuotient K 0 n p = 0 := sorry

/-- The canonical map `grᵖ Kⁿ = Fᵖ Kⁿ / Fᵖ⁺¹ Kⁿ ⟶ Z₀^p / B₀^p` induced by the inclusion of the
stage into the zeroth cycle representative. This is the identification
`E₀^{p,q} = grᵖ K^{p+q}` of Stacks 012M on the explicit representatives. -/
@[stacks 012M "zeroth explicit page is the graded piece"]
noncomputable def Page.Zero.gradedPieceToQuotient (K : FilteredComplex C) (n p : ℤ) :
    (K.gradedPiece p).X n ⟶ Page.Representative.quotient K 0 n p :=
  cokernel.desc ((K.X n).filtration.succInclusion p)
    (Subobject.ofLE ((K.X n).filtration.stage p) (Page.Representative.cycle K 0 n p)
        (Page.Zero.stage_le_cycle K n p) ≫
      Page.Representative.toQuotient K 0 n p)
    (Page.Zero.succInclusion_comp_eq_zero K n p)

/-- The first cycle representative `Z₁^p = (Fᵖ Kⁿ ∩ d⁻¹(Fᵖ⁺¹ Kⁿ⁺¹)) + Fᵖ⁺¹ Kⁿ` lies in the
stage `Fᵖ Kⁿ`. -/
@[stacks 012M "the first cycle representative lies in the stage"]
theorem Page.One.cycle_le_stage (K : FilteredComplex C) (n p : ℤ) :
    Page.Representative.cycle K 1 n p ≤ (K.X n).filtration.stage p := sorry

/-- The class in `grᵖ Kⁿ` of an element of `Z₁^p`. -/
@[stacks 012M "graded class of a first-page cycle representative"]
noncomputable def Page.One.cycleToGradedPiece (K : FilteredComplex C) (n p : ℤ) :
    (Page.Representative.cycle K 1 n p : C) ⟶ (K.gradedPiece p).X n :=
  Subobject.ofLE (Page.Representative.cycle K 1 n p) ((K.X n).filtration.stage p)
      (Page.One.cycle_le_stage K n p) ≫
    cokernel.π ((K.X n).filtration.succInclusion p)

/-- Elements of `Z₁^p` have differential in `Fᵖ⁺¹`, so their graded classes are cycles of the
graded-piece complex. -/
@[stacks 012M "first-page cycle representatives give graded-piece cycles"]
theorem Page.One.cycleToGradedPiece_comp_d (K : FilteredComplex C) (n p : ℤ) :
    Page.One.cycleToGradedPiece K n p ≫ (K.gradedPiece p).d n (n + 1) = 0 := sorry

/-- The cohomology class in `Hⁿ(grᵖ K)` of an element of `Z₁^p`. -/
@[stacks 012M "cohomology class of a first-page cycle representative"]
noncomputable def Page.One.cycleToHomology (K : FilteredComplex C) (n p : ℤ) :
    (Page.Representative.cycle K 1 n p : C) ⟶ (K.gradedPiece p).homology n :=
  (K.gradedPiece p).liftCycles (Page.One.cycleToGradedPiece K n p) (n + 1)
      (CochainComplex.next ℤ n) (Page.One.cycleToGradedPiece_comp_d K n p) ≫
    (K.gradedPiece p).homologyπ n

/-- Classes in `B₁^p = (Fᵖ Kⁿ ∩ d(Fᵖ Kⁿ⁻¹)) + Fᵖ⁺¹ Kⁿ` are graded-piece boundaries. -/
@[stacks 012M "first-page boundaries vanish in graded-piece cohomology"]
theorem Page.One.intersection_comp_cycleToHomology (K : FilteredComplex C) (n p : ℤ) :
    Subobject.ofLE (Page.Representative.boundary K 1 n p ⊓ Page.Representative.cycle K 1 n p)
        (Page.Representative.cycle K 1 n p) _root_.inf_le_right ≫
      Page.One.cycleToHomology K n p = 0 := sorry

/-- The canonical map `Z₁^p / B₁^p ⟶ Hⁿ(grᵖ K)` sending a first-page cycle representative to
its graded cohomology class. This is the identification `E₁^{p,q} = H^{p+q}(grᵖ K)` of
Stacks 012M on the explicit representatives. -/
@[stacks 012M "first explicit page is graded-piece cohomology"]
noncomputable def Page.One.quotientToHomology (K : FilteredComplex C) (n p : ℤ) :
    Page.Representative.quotient K 1 n p ⟶ (K.gradedPiece p).homology n :=
  Subobject.IntersectionQuotient.desc _ _ (Page.One.cycleToHomology K n p)
    (Page.One.intersection_comp_cycleToHomology K n p)

/-! ## Canonical passage from one page to the next -/

/-- A strict cycle for the next page is a cycle representative for the current page. -/
@[stacks 012M "successor strict cycles lie in the current cycle representative"]
theorem Page.Representative.successor_strictCycle_le_cycle
    (K : FilteredComplex C) (r : ℕ) (n p : ℤ) :
    Page.Representative.strictCycle K (r + 1) n p ≤
      Page.Representative.cycle K r n p := sorry

/-- The current-page class of a strict successor-page cycle, expressed in a chosen
representative presentation. -/
@[stacks 012M "successor cycle class in the current page"]
noncomputable def Page.Presentation.successorCycleToPage
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    (A : Page.Presentation K E) (r : ℕ) (p q : ℤ) :
    (Page.Representative.strictCycle K (r + 1) (p + q) p : C) ⟶
      (E.page r).X (p, q) :=
  Subobject.ofLE _ _ (Page.Representative.successor_strictCycle_le_cycle K r (p + q) p) ≫
    Page.Representative.toQuotient K r (p + q) p ≫ (A.entryIso r p q).inv

/-- Strict successor-page cycles give cycles of the current-page differential. This uses
the differential representation carried by the presentation. -/
@[stacks 012M "successor representative classes are current-page cycles"]
theorem Page.Presentation.successorCycleToPage_comp_d
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    (A : Page.Presentation K E) (r : ℕ) (p q : ℤ) (j : ℤ × ℤ) :
    A.successorCycleToPage r p q ≫ (E.page r).d (p, q) j = 0 := sorry

/-- The homology class on page `r` of a strict `(r+1)`-cycle. The map is constructed from
the inclusion of representatives, the supplied page comparison, and the canonical homology
projection; it does not select a comparison isomorphism from an existence assertion. -/
@[stacks 012M "successor cycle class in current-page homology"]
noncomputable def Page.Presentation.successorCycleToHomology
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    (A : Page.Presentation K E) (r : ℕ) (p q : ℤ) :
    (Page.Representative.strictCycle K (r + 1) (p + q) p : C) ⟶
      (E.page r).homology (p, q) :=
  (E.page r).liftCycles (A.successorCycleToPage r p q) _ rfl
      (A.successorCycleToPage_comp_d r p q _) ≫
    (E.page r).homologyπ (p, q)

/-- A chosen association between a filtered complex and a cohomological spectral sequence. It
contains the all-page representative presentation and the zeroth-page graded-piece comparison,
and requires the initial comparisons and every passage from page homology to the next page
to agree with the canonical representative classes of Stacks 012M. -/
@[stacks 012M "spectral sequence associated to a filtered complex"]
structure Association (K : FilteredComplex C)
    (E : CohomologicalSpectralSequence C 0)
    extends Page.Presentation K E, Page.Zero.Comparison K E where
  /-- Under the presentation of the zeroth page, the column comparison identifies
  `E₀^{p,q}` with `grᵖ K^{p+q}` through the canonical map `grᵖ K^{p+q} ⟶ Z₀^{p,q}/B₀^{p,q}`. -/
  columnIso_inv_comp_entryIso : ∀ p q : ℤ,
    (columnIso p).inv.f q ≫
        (CohomologicalSpectralSequence.PageZeroColumn.xIso E p q).hom ≫
        (toPresentation.entryIso 0 p q).hom =
      Page.Zero.gradedPieceToQuotient K (p + q) p
  /-- Under the presentation of the first page, the first-page comparison induced by the
  zeroth page is the canonical map `Z₁^{p,q}/B₁^{p,q} ⟶ H^{p+q}(grᵖ K)`. -/
  entryIso_comp_quotientToHomology : ∀ p q : ℤ,
    (toPresentation.entryIso 1 p q).hom ≫ Page.One.quotientToHomology K (p + q) p =
      (Page.One.iso toComparison p q).hom
  /-- The spectral-sequence structure map sends the homology class of a strict successor
  cycle to its class in the next explicit quotient. This fixes `E.iso` at every page relative
  to the same representative presentation, including the transition from page zero to one. -/
  successorCycleToHomology_comp_iso : ∀ (r : ℕ) (p q : ℤ),
    toPresentation.successorCycleToHomology r p q ≫
        (E.iso (r : ℤ) ((r + 1 : ℕ) : ℤ) (p, q)).hom ≫
        (toPresentation.entryIso (r + 1) p q).hom =
      FilteredObject.Hom.Page.strictCycleToQuotient
        (K.d (p + q - 1) (p + q)) (K.d (p + q) (p + q + 1)) (r + 1) p

/-- The canonical first-page comparison carried by an association. This is the convenient
downstream form of its zeroth-page graded-piece comparison. -/
@[stacks 012M "first-page comparison from an association"]
noncomputable def Association.pageOneIso
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    (A : Association K E) (p q : ℤ) :
    (E.page 1).X (p, q) ≅ (K.gradedPiece p).homology (p + q) :=
  Page.One.iso A.toComparison p q

/-- A selected cohomological spectral sequence together with concrete association data for a
fixed filtered complex. Unlike `IsAssociated`, this is data and can therefore be passed to
constructions that need to retain the chosen sequence and its page comparisons. -/
@[stacks 012M "chosen spectral sequence associated to a filtered complex"]
structure AssociatedSpectralSequence (K : FilteredComplex C) where
  /-- The selected cohomological spectral sequence. -/
  sequence : CohomologicalSpectralSequence C 0
  /-- Concrete association data for the selected spectral sequence. -/
  association : Association K sequence

/-- Bundle specified association data with the spectral sequence to which it applies. -/
@[stacks 012M "chosen spectral sequence associated to a filtered complex"]
def Association.toAssociatedSpectralSequence
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    (A : Association K E) : AssociatedSpectralSequence K where
  sequence := E
  association := A

end FilteredComplex

/-- Stacks 012M: a cohomological spectral sequence is associated to a filtered complex when all
its entries are the explicit subquotients `Zᵣ^{p,q}/Bᵣ^{p,q}`, its differentials admit the
strict-cycle quotient representation of the filtered-complex differential, its zeroth page
is canonically the associated graded complex, and each structure isomorphism from page homology
to the next page preserves the strict-cycle representative classes. -/
@[stacks 012M "spectral sequence associated to a filtered complex"]
def FilteredComplex.IsAssociated (K : FilteredComplex C)
    (E : CohomologicalSpectralSequence C 0) : Prop :=
  Nonempty (FilteredComplex.Association K E)

namespace FilteredComplex

namespace AssociatedSpectralSequence

/-- The selected association data carried by an `AssociatedSpectralSequence` supplies the
corresponding representation-independent proposition. -/
@[stacks 012M "spectral sequence associated to a filtered complex"]
theorem isAssociated {K : FilteredComplex C} (S : AssociatedSpectralSequence K) :
    IsAssociated K S.sequence := sorry

end AssociatedSpectralSequence

/-- The association proposition implies the all-page representative property. -/
@[stacks 012M "association implies an all-page presentation"]
theorem IsAssociated.hasPresentation
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    (h : IsAssociated K E) :
    Page.HasPresentation K E := sorry

/-- The association proposition implies the zeroth-page graded-piece property. -/
@[stacks 012M "association implies a graded zeroth page"]
theorem IsAssociated.isGradedPiece
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    (h : IsAssociated K E) :
    Page.Zero.IsGradedPiece K E := sorry

/-- Every filtered complex admits a cohomological spectral sequence with the explicit `Zᵣ/Bᵣ`
pages, strict-cycle represented differentials, canonical initial comparisons, and coherent
structure isomorphisms on every page. -/
@[stacks 012M "existence of an associated spectral sequence"]
theorem IsAssociated.exists (K : FilteredComplex C) :
    ∃ E : CohomologicalSpectralSequence C 0, IsAssociated K E := sorry

/-- Every filtered complex admits a selected cohomological spectral sequence together with
concrete association data. The result is `Nonempty` because the selection is not canonical. -/
@[stacks 012M "chosen spectral sequence associated to a filtered complex"]
theorem AssociatedSpectralSequence.nonempty (K : FilteredComplex C) :
    Nonempty (AssociatedSpectralSequence K) := sorry

end FilteredComplex

end CategoryTheory
