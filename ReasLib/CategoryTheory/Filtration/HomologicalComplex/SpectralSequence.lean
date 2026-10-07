module

public import ReasLib.CategoryTheory.Filtration.HomologicalComplex.Representatives
public import ReasLib.CategoryTheory.Filtration.HomologicalComplex.TwoStep
public import ReasLib.CategoryTheory.Homology.SpectralSequence.LimitStages
public import ReasLib.CategoryTheory.Subobject.Quotient
public import Mathlib.CategoryTheory.Abelian.CommSq

/-!
# Spectral Sequences of Filtered Differential Objects

This file gives the reusable association API for the spectral sequence of a filtered
differential object.  A page presentation records the explicit quotients `Zᵣ/Bᵣ` and the
induced differentials on every finite page.  An association additionally records the zeroth-page
comparison with the associated graded differential object, from which the usual first-page
comparison is derived.

In particular, zeroth-page data alone is deliberately not an association predicate.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory
namespace HomologicalComplex.Filtered

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))

namespace Page.Representative

/-- The page-`r` cycle representative of a filtered differential object in filtration degree
`p`. -/
@[stacks 012C "finite-page cycle representative"]
abbrev cycle (r : ℕ) (p : ℤ) : Subobject ((K.X PUnit.unit).obj) :=
  (differential K).cycleRepresentative r p

/-- The strict part of the page-cycle representative, before adjoining the filtration-negligible
summand in degree `p + 1`. -/
@[stacks 012C "strict finite-page cycle representative"]
abbrev strictCycle (r : ℕ) (p : ℤ) : Subobject ((K.X PUnit.unit).obj) :=
  FilteredObject.Hom.Page.strictCycle (differential K) r p

/-- The page-`r` boundary representative of a filtered differential object in filtration degree
`p`. -/
@[stacks 012C "finite-page boundary representative"]
abbrev boundary (r : ℕ) (p : ℤ) : Subobject ((K.X PUnit.unit).obj) :=
  (differential K).boundaryRepresentative r p

/-- The page-`r` boundary representative is contained in the matching cycle representative. -/
@[stacks 012C "finite-page boundary containment"]
theorem boundary_le_cycle (r : ℕ) (p : ℤ) :
    boundary K r p ≤ cycle K r p := sorry

/-- The explicit page entry attached to a filtered differential object, represented canonically
as `Zᵣ / (Bᵣ ⊓ Zᵣ)`. The theorem `boundary_le_cycle` identifies this with the textbook quotient
`Zᵣ / Bᵣ` without making the object depend on an unfinished proof. -/
@[stacks 012C "finite-page quotient representative"]
noncomputable abbrev quotient (r : ℕ) (p : ℤ) : C :=
  FilteredObject.Hom.Page.quotient (differential K) (differential K) r p

/-- The canonical quotient map from the cycle representative to
`Page.Representative.quotient K r p`. -/
@[stacks 012C "finite-page quotient projection"]
noncomputable abbrev toQuotient (r : ℕ) (p : ℤ) :
    (cycle K r p : C) ⟶ quotient K r p :=
  FilteredObject.Hom.Page.toQuotient (differential K) (differential K) r p

/-- The proof-free page representative is isomorphic to the textbook quotient `Zᵣ / Bᵣ`. -/
@[stacks 012C "finite-page quotient comparison"]
theorem quotient_isIsomorphic (r : ℕ) (p : ℤ) :
    IsIsomorphic (quotient K r p)
      (cokernel (Subobject.ofLE (boundary K r p) (cycle K r p) (boundary_le_cycle K r p))) := sorry

end Page.Representative

variable {E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0}

namespace Page.Differential

/-- A page differential is represented on strict cycles when its quotient action is induced by
the filtered differential after discarding the filtration-negligible source summand.  The
argument is stated with the local page representatives, which are definitionally the generic
pair quotients for the unique differential object. -/
@[stacks 012C "strict-cycle representation of a finite-page differential"]
def IsRepresented (r : ℕ) (p : ℤ)
    (δ : Page.Representative.quotient K r p ⟶ Page.Representative.quotient K r (p + r)) : Prop :=
  FilteredObject.Hom.Page.Differential.IsRepresented
    (f0 := differential K) (f1 := differential K) (f2 := differential K) r p δ

/-- The filtered differential factors from strict source cycles to strict target cycles at the
shifted filtration degree. -/
@[stacks 012C "strict finite-page differential cycle factorization"]
theorem strictCycle_factors
    (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))
    (r : ℕ) (p : ℤ) :
    (Page.Representative.strictCycle K r (p + r)).Factors
      ((Page.Representative.strictCycle K r p).arrow ≫ (differential K).hom) := sorry

/-- Transport a page differential through chosen `Page.Representative.quotient` presentations. -/
@[stacks 012C "transported finite-page differential"]
noncomputable def transport
    (e : ∀ (r : ℕ) (p : ℤ),
      (E.page r).X p ≅ Page.Representative.quotient K r p)
    (r : ℕ) (p : ℤ) :
    Page.Representative.quotient K r p ⟶
      Page.Representative.quotient K r (p + r) :=
  (e r p).inv ≫ (E.page r).d p (p + r) ≫ (e r (p + r)).hom

end Page.Differential

namespace Page.Differential.IsRepresented

/-- Two strict-cycle represented page differentials of the same filtered differential object are
equal. -/
@[stacks 012C "uniqueness of a strict-cycle represented finite-page differential"]
theorem unique
    {K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1})}
    {r : ℕ} {p : ℤ}
    {δ ε : Page.Representative.quotient K r p ⟶ Page.Representative.quotient K r (p + r)}
    (hδ : Page.Differential.IsRepresented K r p δ)
    (hε : Page.Differential.IsRepresented K r p ε) :
    δ = ε := sorry

/-- Every finite-page differential of a filtered differential object has a strict-cycle
representation. This proposition-level interface does not choose non-Prop data from unfinished
factorization proofs. -/
@[stacks 012C "existence of a strict-cycle represented finite-page differential"]
theorem existsMap
    (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))
    (r : ℕ) (p : ℤ) :
    ∃ δ : Page.Representative.quotient K r p ⟶ Page.Representative.quotient K r (p + r),
      Page.Differential.IsRepresented K r p δ := sorry

/-- The strict-cycle represented finite-page differential is unique. -/
@[stacks 012C "unique existence of a strict-cycle represented finite-page differential"]
theorem existsUniqueMap
    (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))
    (r : ℕ) (p : ℤ) :
    ∃! δ : Page.Representative.quotient K r p ⟶ Page.Representative.quotient K r (p + r),
      Page.Differential.IsRepresented K r p δ := sorry

end Page.Differential.IsRepresented

/-- A morphism between explicit page representatives is induced by a morphism of filtered
differential objects when its unique component induces the corresponding generic map of a
composable filtered pair. -/
@[stacks 012C "finite-page morphism inducedness"]
def Page.Map.IsInduced
    {K L : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1})}
    (α : K ⟶ L) (r : ℕ) (p : ℤ)
    (γ : Page.Representative.quotient K r p ⟶ Page.Representative.quotient L r p) : Prop :=
  FilteredObject.Hom.Page.Map.IsInduced
    (f0 := differential K) (f1 := differential K)
    (g0 := differential L) (g1 := differential L)
    (α.f PUnit.unit) r p γ

namespace Page.Map

/-- A morphism of filtered differential objects maps source page-cycle representatives into
target page-cycle representatives. -/
@[stacks 012C "filtered differential morphism cycle factorization"]
theorem cycle_factors
    {K L : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1})}
    (α : K ⟶ L) (r : ℕ) (p : ℤ) :
    (Page.Representative.cycle L r p).Factors
      ((Page.Representative.cycle K r p).arrow ≫ (α.f PUnit.unit).hom) := sorry

/-- A morphism of filtered differential objects maps source boundary-cycle intersections into
target boundary-cycle intersections. -/
@[stacks 012C "filtered differential morphism intersection factorization"]
theorem intersection_factors
    {K L : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1})}
    (α : K ⟶ L) (r : ℕ) (p : ℤ) :
    (Page.Representative.boundary L r p ⊓ Page.Representative.cycle L r p).Factors
      ((Page.Representative.boundary K r p ⊓
        Page.Representative.cycle K r p).arrow ≫ (α.f PUnit.unit).hom) := sorry

end Page.Map

namespace Page.Map.IsInduced

/-- The identity of an explicit page representative is induced by the identity filtered
differential morphism. -/
@[stacks 012C "identity map of explicit page representatives"]
theorem id
    (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))
    (r : ℕ) (p : ℤ) :
    Page.Map.IsInduced (𝟙 K) r p (𝟙 (Page.Representative.quotient K r p)) := sorry

/-- Maps of explicit page representatives induced by filtered differential morphisms are closed
under composition. -/
@[stacks 012C "composition of explicit page representative maps"]
theorem comp
    {K L M : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1})}
    {α : K ⟶ L} {β : L ⟶ M} {r : ℕ} {p : ℤ}
    {γ : Page.Representative.quotient K r p ⟶ Page.Representative.quotient L r p}
    {δ : Page.Representative.quotient L r p ⟶ Page.Representative.quotient M r p}
    (hγ : Page.Map.IsInduced α r p γ) (hδ : Page.Map.IsInduced β r p δ) :
    Page.Map.IsInduced (α ≫ β) r p (γ ≫ δ) := sorry

/-- Two explicit page-quotient maps induced by the same filtered differential morphism are
equal. -/
@[stacks 012C "uniqueness of finite-page quotient maps of filtered differential morphisms"]
theorem unique
    {K L : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1})}
    {α : K ⟶ L} {r : ℕ} {p : ℤ}
    {γ δ : Page.Representative.quotient K r p ⟶ Page.Representative.quotient L r p}
    (hγ : Page.Map.IsInduced α r p γ) (hδ : Page.Map.IsInduced α r p δ) :
    γ = δ := sorry

/-- Every morphism of filtered differential objects induces a map between the corresponding
explicit finite-page representatives. This statement avoids selecting morphism data from
deferred factorization proofs. -/
@[stacks 012C "existence of finite-page quotient maps of filtered differential morphisms"]
theorem existsMap
    {K L : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1})}
    (α : K ⟶ L) (r : ℕ) (p : ℤ) :
    ∃ γ : Page.Representative.quotient K r p ⟶ Page.Representative.quotient L r p,
      Page.Map.IsInduced α r p γ := sorry

/-- The explicit finite-page map induced by a morphism of filtered differential objects is
unique. -/
@[stacks 012C "unique existence of finite-page quotient maps of filtered differential morphisms"]
theorem existsUniqueMap
    {K L : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1})}
    (α : K ⟶ L) (r : ℕ) (p : ℤ) :
    ∃! γ : Page.Representative.quotient K r p ⟶ Page.Representative.quotient L r p,
      Page.Map.IsInduced α r p γ := sorry

end Page.Map.IsInduced

/-- Chosen page-entry presentations identify every page differential through the strict-cycle
quotient representation of the filtered differential. -/
@[stacks 012C "strict-cycle finite-page representative presentation condition"]
def Page.IsRepresentation
    (e : ∀ (r : ℕ) (p : ℤ),
      (E.page r).X p ≅ Page.Representative.quotient K r p) : Prop :=
  ∀ (r : ℕ) (p : ℤ),
    Page.Differential.IsRepresented K r p
      (Page.Differential.transport K e r p)

/-- A chosen all-page presentation of a spectral sequence by
`Page.Representative.quotient` objects of a filtered differential object. -/
@[stacks 012C "all-page presentation of a filtered differential spectral sequence"]
structure Page.Presentation
    (E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0) where
  /-- The chosen identification of every page entry with its explicit quotient. -/
  pageIso : ∀ (r : ℕ) (p : ℤ),
    (E.page r).X p ≅ Page.Representative.quotient K r p
  /-- Under the chosen identifications, every page differential has the strict-cycle quotient
  representation of `K.d`. -/
  isRepresentation : Page.IsRepresentation K pageIso

/-- The property that a spectral sequence admits an all-page presentation by the explicit
quotients `Zᵣ/Bᵣ`. -/
@[stacks 012C "existence of an all-page filtered differential presentation"]
def Page.HasPresentation
    (E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0) : Prop :=
  Nonempty (Page.Presentation K E)

/-- The zeroth-page complex: its degree-`p` term is `gr^p K`, and its degree-zero differential
is induced by the differential of `K`. -/
@[stacks 012C "zeroth page of a filtered differential spectral sequence"]
noncomputable def Page.Zero.complex : HomologicalComplex C (ComplexShape.up' (0 : ℤ)) where
  X p := (gradedPiece K p).X PUnit.unit
  d p q :=
    if h : p = q then
      (gradedPiece K p).d PUnit.unit PUnit.unit ≫
        eqToHom (congrArg (fun n ↦ (gradedPiece K n).X PUnit.unit) h)
    else
      0
  shape := sorry
  d_comp_d' := sorry

/-- The short complex in the zeroth page at filtration degree `p` is the short complex of the
graded differential object `gr^p K`. -/
noncomputable def Page.Zero.scIso (p : ℤ) :
    (Page.Zero.complex K).sc' p p p ≅
      (gradedPiece K p).sc' PUnit.unit PUnit.unit PUnit.unit :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) sorry sorry

/-- The predecessor of a degree on the zeroth page is that degree itself. -/
theorem Page.Zero.prev_eq (p : ℤ) :
    (ComplexShape.up' (0 : ℤ)).prev p = p := sorry

/-- The successor of a degree on the zeroth page is that degree itself. -/
theorem Page.Zero.next_eq (p : ℤ) :
    (ComplexShape.up' (0 : ℤ)).next p = p := sorry

/-- Zeroth-page homology in degree `p` is the homology of the graded differential object
`gr^p K`. -/
noncomputable def Page.Zero.homologyIso (p : ℤ) :
    (Page.Zero.complex K).homology p ≅ (gradedPiece K p).homology PUnit.unit :=
  (Page.Zero.complex K).homologyIsoSc' p p p (Page.Zero.prev_eq p) (Page.Zero.next_eq p) ≪≫
    ShortComplex.homologyMapIso (Page.Zero.scIso K p) ≪≫
      ((gradedPiece K p).homologyIsoSc' PUnit.unit PUnit.unit PUnit.unit rfl rfl).symm

/-- A zeroth-page comparison induces the canonical first-page identification with the homology
of the graded differential object. -/
noncomputable def Page.One.iso
    (e₀ : E.page 0 ≅ Page.Zero.complex K) (p : ℤ) :
    (E.page 1).X p ≅ (gradedPiece K p).homology PUnit.unit :=
  (E.iso 0 1 p).symm ≪≫
    HomologicalComplex.homologyMapIso e₀ p ≪≫ Page.Zero.homologyIso K p

/-- A chosen association between a filtered differential object and a spectral sequence.  It
contains the all-page `Zᵣ/Bᵣ` presentation and the zeroth-page comparison; the first-page
comparison is derived, while its compatibility with the two-step boundary is stored as a law. -/
@[stacks 012C "spectral sequence associated to a filtered differential object"]
structure Association
    (E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0)
    extends Page.Presentation K E where
  /-- The zeroth page is the associated graded differential object. -/
  pageZeroIso : E.page 0 ≅ Page.Zero.complex K
  /-- Under the induced first-page comparison, `d₁` is the connecting morphism of the canonical
  two-step quotient sequence. -/
  pageOne_d_eq_boundaryMap : ∀ p : ℤ,
    CommSq
      ((E.page 1).d p (p + 1))
      ((Page.One.iso K pageZeroIso p).hom)
      ((Page.One.iso K pageZeroIso (p + 1)).hom)
      (TwoStep.boundary K p rfl)

attribute [stacks 012D] Association.pageOne_d_eq_boundaryMap

/-- The representation-independent proposition that `E` is associated to `K`. -/
@[stacks 012C "association of a filtered differential object and a spectral sequence"]
def Association.IsAssociated
    (E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0) : Prop :=
  Nonempty (Association K E)

/-- A chosen association supplies its all-page presentation. -/
theorem Association.hasPagePresentation (A : Association K E) :
    Page.HasPresentation K E := sorry

/-- The association proposition implies the all-page representative property. -/
theorem Association.IsAssociated.hasPagePresentation
    (h : Association.IsAssociated K E) :
    Page.HasPresentation K E := sorry

/-- The canonical first-page identification with the homology of the graded differential
object. -/
@[stacks 012C "first-page identification with graded homology"]
noncomputable def Association.PageOne.iso
    {K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1})}
    (A : Association K E) (p : ℤ) :
    (E.page 1).X p ≅ (gradedPiece K p).homology PUnit.unit :=
  Page.One.iso K A.pageZeroIso p

/-- Every filtered differential object admits an associated spectral sequence whose finite
pages are the explicit `Zᵣ/Bᵣ` quotients and whose zeroth page is the associated graded
differential object. -/
@[stacks 012C "existence of the filtered differential spectral sequence"]
theorem Association.exists :
    ∃ E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0,
      Association.IsAssociated K E := sorry

/-- Forgetting the zeroth page views a spectral sequence of filtered differential objects as one
starting at page one. -/
@[stacks 012F "page-one presentation of a filtered differential spectral sequence"]
abbrev Page.One.tail
    (E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0) :
    SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 1 :=
  SpectralSequence.Page.One.ofZero E

/-- A graded piece of induced homology is a subquotient of the corresponding limit-page entry
for any explicit limit stages of an associated spectral sequence. -/
@[stacks 012F "homology graded pieces as limit-page subquotients"]
theorem LimitPage.gradedPiece_isSubquotient
    (E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0)
    (hAssoc : Page.HasPresentation K E)
    (L : SpectralSequence.LimitStages (Page.One.tail E)) (p : ℤ) :
    IsSubquotient ((Homology.Filtration.induced K PUnit.unit).gradedPiece p)
      (L.infinityPage p) := sorry

/-- The associated graded of induced homology is degreewise a subquotient of the graded limit
page. -/
@[stacks 012F "associated graded homology as a limit-page subquotient"]
theorem LimitPage.graded_isSubquotient
    (E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0)
    (hAssoc : Page.HasPresentation K E)
    (L : SpectralSequence.LimitStages (Page.One.tail E)) :
    ∀ p : ℤ,
      IsSubquotient ((Homology.Filtration.induced K PUnit.unit).gradedPiece p)
        (L.infinityPageObject p) := sorry

end HomologicalComplex.Filtered
end CategoryTheory
