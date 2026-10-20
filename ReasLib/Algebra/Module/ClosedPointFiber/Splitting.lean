module

public import ReasLib.Algebra.Module.ClosedPointFiber.Visible
public import ReasLib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.Tactic.CrossRefAttribute

/-!
# Splitting free summands from closed-point fibers

This leaf records interpolation of visible fiber classes, codimension control for dependence loci,
and the local free-summand criterion used to split one copy of the base ring.

@stack 0GVA
@stack 0GVB
@stack 0GVC
-/

@[expose] public section

open Order Set TopologicalSpace
open scoped ClosedPointFiber

universe u v

namespace Module

/-- A module has a free direct summand of rank greater than `d` when it splits as a product of a
free module of rank `r > d` and a complementary submodule. -/
@[stacks 0GVC "free summand rank bound"]
def HasFreeSummandRankGT
    (S : Type u) [CommRing S] (P : Type v) [AddCommGroup P] [Module S P]
    (d : ℕ) : Prop :=
  ∃ r : ℕ, d < r ∧
    ∃ C : Submodule S P, Nonempty (P ≃ₗ[S] (Fin r → S) × C)

end Module

namespace Module.ClosedFiber

variable {R : Type u} [CommRing R]
variable {N : Type v} [AddCommGroup N] [Module R N]

local notation "Ω" => closedPoints (PrimeSpectrum R)

/-- Lemma 15.128.3, tag 0GVA: prescribed visible classes at finitely many pairwise distinct
closed points are simultaneously represented by one global section. -/
@[stacks 0GVA "interpolation of visible fiber classes"]
theorem existsSectionWithPrescribedVisibleClasses
    [Module.FinitePresentation R N]
    {n : ℕ} (points : Fin n → Ω)
    (hpoints : Pairwise fun i j ↦ points i ≠ points j)
    (values : ∀ i, Visible N (points i)) :
    ∃ s : N, ∀ i, visibleClass (points i) s = values i := sorry
-- Proof strategy: lift every visible value to the full quotient fiber, use pairwise comaximality
-- of the distinct maximal ideals and the module Chinese remainder theorem to realize all fiber
-- values by one element of `N`, then project to each visible quotient.

/-- The closed-point locus where the visible classes of a finite family of sections are linearly
dependent. -/
@[stacks 0GVB "section dependence locus"]
def sectionDependenceLocus {h : ℕ} (sections : Fin h → N) : Set Ω :=
  {x | ¬ LinearIndependent κ(x) (visibleClass x ∘ sections)}

/-- A subset of the closed-point space has irreducible components of codimension at least `k`
when each maximal irreducible closed subset contained in it has coheight at least `k`. -/
@[stacks 0GVB "component codimension bound"]
def irreducibleComponentsCodimAtLeast (k : ℕ) (F : Set Ω) : Prop :=
  ∀ Z : IrreducibleCloseds Ω,
    Maximal (fun Y : IrreducibleCloseds Ω ↦ (Y : Set Ω) ⊆ F) Z →
      (k : ℕ∞) ≤ coheight Z

/-- A section extending prescribed closed-point fiber classes, together with a closed exceptional
locus controlling the new dependence locus in codimension. -/
@[stacks 0GVB "codimension-controlled extension data"]
structure CodimControlledExtension {h n : ℕ}
    (sections : Fin h → N) (F : Set Ω) (points : Fin n → Ω)
    (values : ∀ i, Visible N (points i)) (k : ℕ) where
  /-- The additional global section. -/
  newSection : N
  /-- The auxiliary closed subset outside which the enlarged family is independent away from
  `F`. -/
  exceptionalLocus : Set Ω
  /-- The auxiliary exceptional locus is closed. -/
  exceptionalLocus_isClosed : IsClosed exceptionalLocus
  /-- Proposition 15.128.4 (a): the additional section represents every prescribed visible
  class. -/
  prescribedValues : ∀ i, visibleClass (points i) newSection = values i
  /-- Proposition 15.128.4 (b): the enlarged dependence locus is contained in the union of the
  original closed set and the exceptional locus. -/
  dependenceLocus_subset :
    sectionDependenceLocus (Fin.snoc sections newSection) ⊆ F ∪ exceptionalLocus
  /-- Proposition 15.128.4 (c): every irreducible component of the exceptional locus has
  codimension at least `k`. -/
  components_codimAtLeast : irreducibleComponentsCodimAtLeast k exceptionalLocus

/-- Proposition 15.128.4, clauses (a)-(c): under the visible-fiber dimension bound `h + k`, one
can prescribe a new section at finitely many closed points while confining the enlarged dependence
locus to the original closed set and a closed set whose components have codimension at least `k`. -/
@[stacks 0GVB "Proposition 15.128.4, clauses (a)-(c)"]
theorem existsSectionWithCodimControlledDependenceLocus
    [Module.FinitePresentation R N] [NoetherianSpace Ω]
    {h n k : ℕ} (sections : Fin h → N) {F : Set Ω} (hFclosed : IsClosed F)
    (hdependence : sectionDependenceLocus sections ⊆ F)
    (points : Fin n → Ω) (hpoints : Pairwise fun i j ↦ points i ≠ points j)
    (hpointsF : ∀ i, points i ∈ F) (values : ∀ i, Visible N (points i))
    (hdim : ∀ x : Ω, h + k ≤ Module.finrank κ(x) (Visible N x)) :
    Nonempty (CodimControlledExtension sections F points values k) := sorry
-- Proof strategy: by Noetherian induction, list the finitely many generic points of dependence
-- components of codimension below `k`. At those points choose visible values outside the current
-- spans, combine them with the prescribed values using interpolation, and take the closed residual
-- dependence locus; the dimension bound excludes all newly retained low-codimension components.

/-- A module has a local free summand of rank greater than `d` at a closed point when its
localization at the corresponding maximal ideal has such a summand. -/
@[stacks 0GVC "local free summand rank bound"]
def HasLocalFreeSummandRankGT (N : Type v) [AddCommGroup N] [Module R N]
    (x : Ω) (d : ℕ) : Prop :=
  Module.HasFreeSummandRankGT (Localization.AtPrime x.1.asIdeal)
    (LocalizedModule.AtPrime x.1.asIdeal N) d

/-- For a finitely presented module, the existence of a local free summand of rank greater than
`d` is detected by the dimension of the visible closed-point fiber. -/
@[stacks 0GVC "local free summand criterion"]
theorem hasLocalFreeSummandRankGT_iff_finrank_visible
    [Module.FinitePresentation R N] (x : Ω) (d : ℕ) :
    HasLocalFreeSummandRankGT N x d ↔ d < Module.finrank κ(x) (Visible N x) := sorry
-- Proof strategy: localize the finite presentation at the maximal ideal of `x`; the local
-- free-summand rank criterion is detected by independent residue classes, and
-- `selectedSectionsSplitAfterInverting_iff_linearIndependent` identifies those classes with the
-- visible fiber.

/-- Theorem 15.128.5, tag 0GVC: if the Noetherian closed-point space has finite dimension `d` and
every maximal localization of `N` has a free direct summand of rank greater than `d`, then one copy
of `R` splits from `N`. -/
@[stacks 0GVC "splitting a free rank-one summand from local free summands"]
theorem existsLinearEquivProdOfLocalFreeSummandRankGT
    [Module.FinitePresentation R N]
    {d : ℕ} [NoetherianSpace Ω] (hdim : topologicalKrullDim Ω = d)
    (hlocal : ∀ x : Ω, HasLocalFreeSummandRankGT N x d) :
    ∃ N' : Submodule R N, Nonempty (N ≃ₗ[R] R × N') := sorry
-- Proof strategy: translate the local summand hypotheses to visible dimension bounds, apply the
-- codimension-controlled extension theorem to an initially empty family, and use
-- `topologicalKrullDim Ω = d` to eliminate the final exceptional locus. The resulting globally
-- unimodular section and linear form split `R` from `N`, with the kernel as complement.

/-- The visible-fiber form of the free-summand theorem, obtained through
`hasLocalFreeSummandRankGT_iff_finrank_visible`. -/
@[stacks 0GVC "visible-fiber free summand criterion"]
theorem existsLinearEquivProdOfFinrankVisibleGTDimension
    [Module.FinitePresentation R N]
    {d : ℕ} [NoetherianSpace Ω] (hdim : topologicalKrullDim Ω = d)
    (hvisible : ∀ x : Ω, d < Module.finrank κ(x) (Visible N x)) :
    ∃ N' : Submodule R N, Nonempty (N ≃ₗ[R] R × N') := sorry
-- Proof strategy: convert `hvisible` pointwise with
-- `hasLocalFreeSummandRankGT_iff_finrank_visible`, then apply
-- `existsLinearEquivProdOfLocalFreeSummandRankGT`.

end Module.ClosedFiber
