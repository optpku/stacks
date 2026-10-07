module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence.PageRepresentatives

/-!
# Presentations of Filtered-Complex Spectral Sequences

This file packages entrywise identifications of a spectral sequence with the explicit page
quotients of a filtered complex and provides transport of differentials and morphisms through
such presentations.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredComplex

/-- Transport the differential on the `r`-th spectral-sequence page to the explicit
`Zᵣ/Bᵣ` representatives in total degrees `n` and `n+1`. -/
@[stacks 012M "transported finite-page differential"]
noncomputable def Page.Differential.transport (K : FilteredComplex C)
    (E : CohomologicalSpectralSequence C 0)
    (e : ∀ (r : ℕ) (n p : ℤ),
      (E.page r).X (p, n - p) ≅ Page.Representative.quotient K r n p)
    (r : ℕ) (n p : ℤ) :
    Page.Representative.quotient K r n p ⟶
      Page.Representative.quotient K r (n + 1) (p + r) :=
  (e r n p).inv ≫
    (E.page r).d (p, n - p) (p + r, n + 1 - (p + r)) ≫
    (e r (n + 1) (p + r)).hom

/-- A family of page-entry isomorphisms represents `E` by the explicit page quotients of `K`
when every transported page differential has the strict-cycle quotient representation of the
filtered-complex differential. -/
@[stacks 012M "strict-cycle representation of finite-page differentials"]
def Page.IsRepresentation (K : FilteredComplex C) (E : CohomologicalSpectralSequence C 0)
    (e : ∀ (r : ℕ) (n p : ℤ),
      (E.page r).X (p, n - p) ≅ Page.Representative.quotient K r n p) : Prop :=
  ∀ (r : ℕ) (n p : ℤ),
    Page.Differential.IsRepresented K r n p (Page.Differential.transport K E e r n p)

/-- Every entry of `E` has the explicit `Zᵣ/Bᵣ` presentation associated to `K`, and under
these presentations every page differential is represented through the strict-cycle quotient
cover of `K.d`. -/
@[stacks 012M "explicit representative presentation of a spectral sequence"]
structure Page.Presentation (K : FilteredComplex C)
    (E : CohomologicalSpectralSequence C 0) where
  /-- The chosen identification of every page entry with its explicit quotient. -/
  pageIso : ∀ (r : ℕ) (n p : ℤ),
    (E.page r).X (p, n - p) ≅ Page.Representative.quotient K r n p
  /-- Under the chosen identifications, each page differential has the strict-cycle quotient
  representation of `K.d`. -/
  isRepresentation : Page.IsRepresentation K E pageIso

/-- The presentation isomorphism at bidegree `(p,q)`, with its total degree written directly as
`p + q`. -/
@[stacks 012M "bidegree form of a representative presentation"]
noncomputable def Page.Presentation.entryIso
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    (A : Page.Presentation K E) (r : ℕ) (p q : ℤ) :
    (E.page r).X (p, q) ≅ Page.Representative.quotient K r (p + q) p :=
  eqToIso (congrArg (fun q' : ℤ ↦ (E.page r).X (p, q')) (add_sub_cancel_left p q)).symm ≪≫
    A.pageIso r (p + q) p

/-- The property that a spectral sequence admits an all-page presentation by explicit
`Zᵣ/Bᵣ` quotients. -/
@[stacks 012M "explicit representative presentation exists"]
def Page.HasPresentation (K : FilteredComplex C)
    (E : CohomologicalSpectralSequence C 0) : Prop :=
  Nonempty (Page.Presentation K E)

/-- A chosen page presentation witnesses the corresponding representation-independent
property. -/
theorem Page.Presentation.hasPresentation
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    (A : Page.Presentation K E) :
    Page.HasPresentation K E := sorry

/-- Transport a page component of a spectral-sequence morphism through chosen explicit
`Zᵣ/Bᵣ` presentations of its source and target. -/
@[stacks 012M "transported finite-page representative map"]
noncomputable def Page.Representative.transport {K L : FilteredComplex C}
    {E E' : CohomologicalSpectralSequence C 0}
    (eK : ∀ (r : ℕ) (n p : ℤ),
      (E.page r).X (p, n - p) ≅ Page.Representative.quotient K r n p)
    (eL : ∀ (r : ℕ) (n p : ℤ),
      (E'.page r).X (p, n - p) ≅ Page.Representative.quotient L r n p)
    (φ : E ⟶ E') (r : ℕ) (n p : ℤ) :
    Page.Representative.quotient K r n p ⟶ Page.Representative.quotient L r n p :=
  (eK r n p).inv ≫ (φ.hom r).f (p, n - p) ≫ (eL r n p).hom

/-- Transporting the identity spectral-sequence map through one representative presentation is
the identity map of the corresponding quotient representative. -/
@[simp, stacks 012M "identity transport of page representatives"]
theorem Page.Representative.transport_id {K : FilteredComplex C}
    {E : CohomologicalSpectralSequence C 0}
    (e : ∀ (r : ℕ) (n p : ℤ),
      (E.page r).X (p, n - p) ≅ Page.Representative.quotient K r n p)
    (r : ℕ) (n p : ℤ) :
    Page.Representative.transport e e (𝟙 E) r n p =
      𝟙 (Page.Representative.quotient K r n p) := sorry

/-- Transporting a composite spectral-sequence map through representative presentations agrees
with composing the two transported maps. -/
@[simp, stacks 012M "composition of transported page representatives"]
theorem Page.Representative.transport_comp {K L M : FilteredComplex C}
    {E E' E'' : CohomologicalSpectralSequence C 0}
    (eK : ∀ (r : ℕ) (n p : ℤ),
      (E.page r).X (p, n - p) ≅ Page.Representative.quotient K r n p)
    (eL : ∀ (r : ℕ) (n p : ℤ),
      (E'.page r).X (p, n - p) ≅ Page.Representative.quotient L r n p)
    (eM : ∀ (r : ℕ) (n p : ℤ),
      (E''.page r).X (p, n - p) ≅ Page.Representative.quotient M r n p)
    (φ : E ⟶ E') (ψ : E' ⟶ E'') (r : ℕ) (n p : ℤ) :
    Page.Representative.transport eK eM (φ ≫ ψ) r n p =
      Page.Representative.transport eK eL φ r n p ≫
        Page.Representative.transport eL eM ψ r n p := sorry

end FilteredComplex

end CategoryTheory
