/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence
public import ReasLib.CategoryTheory.Filtration.Complex.MorphismShift
public import ReasLib.CategoryTheory.Filtration.HomologicalComplex.TwoStep.Naturality
public import Mathlib.Algebra.Homology.HomologySequence

/-!
# The First Page of a Filtered Complex

This file gives the concrete boundary-map model for the first page of the spectral sequence of a
filtered cochain complex.  The construction is organized around the canonical two-step quotient
sequence

`0 ⟶ K.gradedPiece (p+1) ⟶ K.stage p / K.stage (p+2) ⟶ K.gradedPiece p ⟶ 0`.

It also develops the more specialized API for a differential which raises the filtration.  In
that case the differentials on the graded-piece complexes vanish, and the first differential is
the map on graded pieces induced by the original differential.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace FilteredComplex

/-! ## The explicit boundary page -/

namespace Page.One

namespace Boundary

variable [Abelian C]

/-- Reindexing the target of the generic two-step connecting morphism from total degree to
bidegree does not change its underlying object. -/
theorem target_eq (K : FilteredComplex C) (p q : ℤ) :
    (K.gradedPiece (p + 1)).homology (p + q + 1) =
      (K.gradedPiece (p + 1)).homology ((p + 1) + q) := sorry

/-- The generic two-step connecting morphism written in cohomological bidegrees
`(p, q) ⟶ (p + 1, q)`. -/
@[stacks 012N "the first differential is the boundary map"]
noncomputable def bidegree (K : FilteredComplex C) (p q : ℤ) :
    (K.gradedPiece p).homology (p + q) ⟶
      (K.gradedPiece (p + 1)).homology ((p + 1) + q) :=
  HomologicalComplex.Filtered.TwoStep.boundary K p
      (ComplexShape.up_mk (p + q) (p + q + 1) rfl) ≫
    eqToHom (target_eq K p q)

/-- The bidegree form of the first boundary map is natural in filtered-complex morphisms. -/
@[reassoc, stacks 012N "naturality of the first boundary map"]
theorem naturality {K L : FilteredComplex C} (f : K ⟶ L) (p q : ℤ) :
    HomologicalComplex.homologyMap (FilteredComplex.gradedPieceMap f p) (p + q) ≫
        bidegree L p q =
      bidegree K p q ≫
        HomologicalComplex.homologyMap (FilteredComplex.gradedPieceMap f (p + 1))
          ((p + 1) + q) := sorry

end Boundary

namespace Differential

variable [Abelian C]

/-- The target of the boundary differential has the object prescribed by the target bidegree. -/
theorem target_eq (K : FilteredComplex C) {pq pq' : ℤ × ℤ}
    (h : (pq.1 + 1, pq.2) = pq') :
    (K.gradedPiece (pq.1 + 1)).homology ((pq.1 + 1) + pq.2) =
      (K.gradedPiece pq'.1).homology (pq'.1 + pq'.2) := sorry

/-- The differential of the explicit boundary model for the first page. -/
@[stacks 012N "differential of the boundary-model first page"]
noncomputable def map (K : FilteredComplex C) (pq pq' : ℤ × ℤ) :
    (K.gradedPiece pq.1).homology (pq.1 + pq.2) ⟶
      (K.gradedPiece pq'.1).homology (pq'.1 + pq'.2) :=
  if h : (pq.1 + 1, pq.2) = pq' then
    Boundary.bidegree K pq.1 pq.2 ≫ eqToHom (target_eq K h)
  else
    0

/-- The explicit first-page differential vanishes away from its prescribed bidegree. -/
theorem shape (K : FilteredComplex C) (pq pq' : ℤ × ℤ)
    (h : ¬ (ComplexShape.up' (⟨(1 : ℤ), 0⟩ : ℤ × ℤ)).Rel pq pq') :
    map K pq pq' = 0 := sorry

/-- Two consecutive differentials in the explicit boundary page compose to zero. -/
theorem comp (K : FilteredComplex C) (pq pq' pq'' : ℤ × ℤ)
    (h : (ComplexShape.up' (⟨(1 : ℤ), 0⟩ : ℤ × ℤ)).Rel pq pq')
    (h' : (ComplexShape.up' (⟨(1 : ℤ), 0⟩ : ℤ × ℤ)).Rel pq' pq'') :
    map K pq pq' ≫ map K pq' pq'' = 0 := sorry

end Differential

variable [Abelian C]

/-- The explicit first page whose entries are graded-piece cohomology and whose differential is
the connecting morphism of the generic two-step quotient sequence. -/
@[stacks 012N "the boundary-map model of the first page"]
noncomputable def complex (K : FilteredComplex C) :
    HomologicalComplex C (ComplexShape.up' (⟨(1 : ℤ), 0⟩ : ℤ × ℤ)) where
  X pq := (K.gradedPiece pq.1).homology (pq.1 + pq.2)
  d := Differential.map K
  shape := Differential.shape K
  d_comp_d' := Differential.comp K

/-- On its nonzero bidegree, the differential of the explicit first page is the boundary map. -/
theorem d (K : FilteredComplex C) (p q : ℤ) :
    (complex K).d (p, q) (p + 1, q) = Boundary.bidegree K p q := sorry

/-- The component on the explicit first page induced by a filtered-complex morphism. -/
@[stacks 012N "map on the boundary-model first page"]
noncomputable def mapComponent {K L : FilteredComplex C}
    (f : K ⟶ L) (pq : ℤ × ℤ) :
    (complex K).X pq ⟶ (complex L).X pq :=
  HomologicalComplex.homologyMap (FilteredComplex.gradedPieceMap f pq.1) (pq.1 + pq.2)

/-- The maps induced on explicit first-page entries commute with the boundary differentials. -/
@[reassoc, stacks 012N "naturality of the boundary-model first-page differential"]
theorem map_comm {K L : FilteredComplex C} (f : K ⟶ L) (pq pq' : ℤ × ℤ)
    (hpq : (ComplexShape.up' (⟨(1 : ℤ), 0⟩ : ℤ × ℤ)).Rel pq pq') :
    mapComponent f pq ≫ (complex L).d pq pq' =
      (complex K).d pq pq' ≫ mapComponent f pq' := sorry

/-- The map of explicit boundary-model first pages induced by a filtered-complex morphism. -/
@[stacks 012N "map of boundary-model first pages"]
noncomputable def map {K L : FilteredComplex C} (f : K ⟶ L) :
    complex K ⟶ complex L where
  f := mapComponent f
  comm' := fun pq pq' hpq ↦ map_comm f pq pq' hpq

/-- The map of explicit first pages induced by an identity is the identity. -/
@[simp, stacks 012N "identity map of boundary-model first pages"]
theorem map_id (K : FilteredComplex C) : map (𝟙 K) = 𝟙 (complex K) := sorry

/-- The map of explicit first pages induced by a composite is the composite of the two maps. -/
@[simp, stacks 012N "composition of boundary-model first-page maps"]
theorem map_comp {K L M : FilteredComplex C} (f : K ⟶ L) (g : L ⟶ M) :
    map (f ≫ g) = map f ≫ map g := sorry

/-- The functor sending a filtered cochain complex to its explicit boundary-model first page. -/
@[stacks 012N "boundary-model first-page functor"]
noncomputable def functor :
    FilteredComplex C ⥤ HomologicalComplex C
      (ComplexShape.up' (⟨(1 : ℤ), 0⟩ : ℤ × ℤ)) where
  obj K := complex K
  map f := map f
  map_id K := map_id K
  map_comp f g := map_comp f g

namespace Functor

/-- The explicit first-page functor evaluates to the boundary-model first page. -/
@[simp, stacks 012N "object of the boundary-model first-page functor"]
theorem obj (K : FilteredComplex C) : (functor).obj K = complex K := sorry

/-- The explicit first-page functor maps a filtered-complex morphism by the boundary-model map. -/
@[simp, stacks 012N "map of the boundary-model first-page functor"]
theorem map {K L : FilteredComplex C} (f : K ⟶ L) :
    (functor).map f = Page.One.map f := sorry

end Functor

end Page.One

/-! ## Differentials which raise the filtration -/

namespace RaisesFiltration

section GradedPiece

variable [HasZeroMorphisms C] [HasCokernels C] {K : FilteredComplex C}

/-- A differential which raises the filtration induces the zero differential on every
graded-piece complex. -/
@[stacks 012N "the differential on every graded piece is zero"]
theorem gradedPiece_d_eq_zero (hK : K.RaisesFiltration) (n n' p : ℤ) :
    (K.gradedPiece p).d n n' = 0 := sorry

/-- The target of the induced graded-piece map in total degree has the expected target
bidegree. -/
theorem bidegreeMapTarget_eq (hK : K.RaisesFiltration) (p q : ℤ) :
    (K.gradedPiece (p + 1)).X (p + q + 1) =
      (K.gradedPiece (p + 1)).X ((p + 1) + q) := sorry

/-- The map induced by the differential on graded pieces, written in bidegrees
`(p,q) ⟶ (p+1,q)`. -/
@[stacks 012N "first-page map induced by a filtration-raising differential"]
noncomputable def bidegreeMap (hK : K.RaisesFiltration) (p q : ℤ) :
    (K.gradedPiece p).X (p + q) ⟶ (K.gradedPiece (p + 1)).X ((p + 1) + q) :=
  (hK (p + q)).gradedPieceMap p ≫ eqToHom (bidegreeMapTarget_eq hK p q)

/-- The bidegree map induced by a filtration-raising differential is independent of the proof
that the differential raises the filtration. -/
@[stacks 012N "proof irrelevance for the raised first-page map"]
theorem bidegreeMap_proof_irrel (hK hK' : K.RaisesFiltration) (p q : ℤ) :
    hK.bidegreeMap p q = hK'.bidegreeMap p q := sorry

end GradedPiece

namespace Page.One

variable [Abelian C] {K : FilteredComplex C}

/-- When the differential raises the filtration, first-page cohomology is canonically the
corresponding graded-piece object. -/
@[stacks 012N "the first page for a filtration-raising differential"]
noncomputable def homologyIso (hK : K.RaisesFiltration) (p q : ℤ) :
    (K.gradedPiece p).homology (p + q) ≅ (K.gradedPiece p).X (p + q) :=
  ((K.gradedPiece p).isoHomologyπ (p + q - 1) (p + q)
      (CochainComplex.prev ℤ (p + q))
      (hK.gradedPiece_d_eq_zero (p + q - 1) (p + q) p)).symm ≪≫
    (K.gradedPiece p).iCyclesIso (p + q) (p + q + 1)
      (CochainComplex.next ℤ (p + q))
      (hK.gradedPiece_d_eq_zero (p + q) (p + q + 1) p)

/-- Composing the associated spectral-sequence comparison with `homologyIso` identifies the
first page directly with the graded-piece objects. -/
@[stacks 012N "first-page comparison for a filtration-raising differential"]
noncomputable def associatedIso (hK : K.RaisesFiltration)
    {E : CohomologicalSpectralSequence C 0} (A : FilteredComplex.Association K E)
    (p q : ℤ) :
    (E.page 1).X (p, q) ≅ (K.gradedPiece p).X (p + q) :=
  A.pageOneIso p q ≪≫ homologyIso hK p q

end Page.One

end RaisesFiltration

/-! ## Comparison with an associated spectral sequence -/

namespace Page.One

/-- The first differential of an associated spectral sequence is the connecting morphism of the
canonical two-step quotient sequence. -/
@[stacks 012N "the first differential is the boundary map"]
theorem d_eq_boundary [Abelian C]
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    (A : FilteredComplex.Association K E) (p q : ℤ) :
    CommSq
      ((E.page 1).d (p, q) (p + 1, q))
      ((A.pageOneIso p q).hom)
      ((A.pageOneIso (p + 1) q).hom)
      (Boundary.bidegree K p q) := sorry

/-- The pointwise first-page comparisons carried by an association commute with every
differential of the explicit boundary-model first page. -/
@[reassoc, stacks 012N "differential compatibility of the first-page comparison"]
theorem associatedIso_comm [Abelian C]
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    (A : FilteredComplex.Association K E) (pq pq' : ℤ × ℤ)
    (hpq : (ComplexShape.up' (⟨(1 : ℤ), 0⟩ : ℤ × ℤ)).Rel pq pq') :
    (A.pageOneIso pq.1 pq.2).hom ≫ (complex K).d pq pq' =
      (E.page 1).d pq pq' ≫ (A.pageOneIso pq'.1 pq'.2).hom := sorry

/-- The first page of an associated spectral sequence is canonically the explicit
boundary-model first page. -/
@[stacks 012N "first-page complex comparison"]
noncomputable def associatedIso [Abelian C]
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    (A : FilteredComplex.Association K E) :
    E.page 1 ≅ complex K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun pq ↦ A.pageOneIso pq.1 pq.2)
    (fun pq pq' hpq ↦ associatedIso_comm A pq pq' hpq)

/-- The component of the first-page complex comparison is the associated pointwise
first-page comparison. -/
@[simp, stacks 012N "component of the first-page complex comparison"]
theorem associatedIso_app [Abelian C]
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    (A : FilteredComplex.Association K E) (p q : ℤ) :
    HomologicalComplex.Hom.isoApp (associatedIso A) (p, q) = A.pageOneIso p q := sorry

/-- The first-page complex comparisons are natural for association-induced maps of spectral
sequences. -/
@[reassoc, stacks 012O "naturality of the first-page complex comparison"]
theorem associatedIso_hom_naturality [Abelian C]
    {K L : FilteredComplex C} {E E' : CohomologicalSpectralSequence C 0}
    {A : FilteredComplex.Association K E} {B : FilteredComplex.Association L E'}
    {α : K ⟶ L} (φ : FilteredComplex.Association.Hom A B α) :
    φ.hom.hom 1 ≫ (associatedIso B).hom = (associatedIso A).hom ≫ map α := sorry

/-- The inverse first-page complex comparisons are natural for association-induced maps of
spectral sequences. -/
@[reassoc, stacks 012O "inverse naturality of the first-page complex comparison"]
theorem associatedIso_inv_naturality [Abelian C]
    {K L : FilteredComplex C} {E E' : CohomologicalSpectralSequence C 0}
    {A : FilteredComplex.Association K E} {B : FilteredComplex.Association L E'}
    {α : K ⟶ L} (φ : FilteredComplex.Association.Hom A B α) :
    map α ≫ (associatedIso B).inv = (associatedIso A).inv ≫ φ.hom.hom 1 := sorry

/-- Conjugating the explicit boundary-model map by the first-page complex comparisons recovers
the underlying first-page morphism. -/
@[reassoc, stacks 012O "computation of the first-page complex map"]
theorem associatedIso_naturality_inv [Abelian C]
    {K L : FilteredComplex C} {E E' : CohomologicalSpectralSequence C 0}
    {A : FilteredComplex.Association K E} {B : FilteredComplex.Association L E'}
    {α : K ⟶ L} (φ : FilteredComplex.Association.Hom A B α) :
    (associatedIso A).hom ≫ map α ≫ (associatedIso B).inv = φ.hom.hom 1 := sorry

/-- If the differential raises the filtration, then under the canonical first-page
identifications the first differential is the map on graded pieces induced by the original
differential. -/
@[stacks 012N "the first differential when the filtration is raised"]
theorem d_eq_raisedGradedPieceMap [Abelian C]
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    (A : FilteredComplex.Association K E) (hK : K.RaisesFiltration) (p q : ℤ) :
    CommSq
      ((E.page 1).d (p, q) (p + 1, q))
      ((RaisesFiltration.Page.One.associatedIso hK A p q).hom)
      ((RaisesFiltration.Page.One.associatedIso hK A (p + 1) q).hom)
      (hK.bidegreeMap p q) := sorry

end Page.One

end FilteredComplex

end CategoryTheory
