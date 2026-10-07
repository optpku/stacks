module

public import stacks_project.Chap98.Lemma_98_19_1
import Mathlib.Tactic.CrossRefAttribute

/-!
# Infinite first-order thickenings detecting failure of versality

On a locally Noetherian base, a groupoid fibration with (RS*) that fails to be
versal at infinitely many pairwise non-specializing finite type points of an
affine finite-type source admits an infinite chain of first-order thickenings
with residue-field kernels and no local retractions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open RingedSpace.Module
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- Existence of an open neighbourhood `W ⊆ T` of the image of `u` and a
morphism `β : y|_W ⟶ x` such that the restriction `ρ` of `φ : x ⟶ y` to
`U ∩ W` satisfies `ρ ≫ β` equal to the canonical morphism `x|_{U ∩ W} ⟶ x`. -/
def existsLocalRetraction {S U T : Scheme.{u}} {X : GroupoidsOver S}
    {hU : U ⟶ S} {hT : T ⟶ S} {i : U ⟶ T} (hi : i ≫ hT = hU)
    {x y : X.total} (hx : X.p.obj x = Over.mk hU) (hy : X.p.obj y = Over.mk hT)
    (φ : x ⟶ y) (u : U) : Prop :=
  ∃ (W : T.Opens), i.base u ∈ W ∧
    ∃ (β : (Chosen.reindexObj X.p (openOverHom hT W) ⟨y, hy⟩).1 ⟶ x)
      (ρ : (Chosen.reindexObj X.p (openOverHom hU (i ⁻¹ᵁ W)) ⟨x, hx⟩).1 ⟶
        (Chosen.reindexObj X.p (openOverHom hT W) ⟨y, hy⟩).1),
      X.p.IsHomLift (restrictOpenOverHom hi W) ρ ∧
        ρ ≫ Chosen.cartesianHom X.p (openOverHom hT W) ⟨y, hy⟩ =
          Chosen.cartesianHom X.p (openOverHom hU (i ⁻¹ᵁ W)) ⟨x, hx⟩ ≫ φ ∧
        ρ ≫ β =
          Chosen.cartesianHom X.p (openOverHom hU (i ⁻¹ᵁ W)) ⟨x, hx⟩

/-- `existsLocalRetraction` is the open-neighbourhood retraction package for
`φ` at `u`. -/
theorem existsLocalRetraction_iff {S U T : Scheme.{u}} {X : GroupoidsOver S}
    {hU : U ⟶ S} {hT : T ⟶ S} {i : U ⟶ T} (hi : i ≫ hT = hU)
    {x y : X.total} (hx : X.p.obj x = Over.mk hU) (hy : X.p.obj y = Over.mk hT)
    (φ : x ⟶ y) (u : U) :
    existsLocalRetraction hi hx hy φ u ↔
      ∃ (W : T.Opens), i.base u ∈ W ∧
        ∃ (β : (Chosen.reindexObj X.p (openOverHom hT W) ⟨y, hy⟩).1 ⟶ x)
          (ρ : (Chosen.reindexObj X.p (openOverHom hU (i ⁻¹ᵁ W)) ⟨x, hx⟩).1 ⟶
            (Chosen.reindexObj X.p (openOverHom hT W) ⟨y, hy⟩).1),
          X.p.IsHomLift (restrictOpenOverHom hi W) ρ ∧
            ρ ≫ Chosen.cartesianHom X.p (openOverHom hT W) ⟨y, hy⟩ =
              Chosen.cartesianHom X.p (openOverHom hU (i ⁻¹ᵁ W)) ⟨x, hx⟩ ≫ φ ∧
            ρ ≫ β =
              Chosen.cartesianHom X.p (openOverHom hU (i ⁻¹ᵁ W)) ⟨x, hx⟩ :=
  sorry

/-- The kernel of `i` as a module sheaf is the residue-field skyscraper at the
image of `u`. This encodes the short exact sequence
`0 ⟶ κ(u) ⟶ 𝒪_T ⟶ 𝒪_U ⟶ 0`. -/
def isResidueFieldKernel {U T : Scheme.{u}} (i : U ⟶ T) (u : U) : Prop :=
  Nonempty (i.ker.toModule ≅ residueFieldSkyscraper i u)

/-- `isResidueFieldKernel i u` means the kernel of `i` is isomorphic to the
residue-field skyscraper at the image of `u`. -/
theorem isResidueFieldKernel_iff {U T : Scheme.{u}} (i : U ⟶ T) (u : U) :
    isResidueFieldKernel i u ↔
      Nonempty (i.ker.toModule ≅ residueFieldSkyscraper i u) :=
  sorry

/-- Lemma 98.20.1: if `S` is locally Noetherian, `X` is a category fibred in
groupoids over `(Sch/S)_fppf` having (RS*), `x` lies over an affine finite-type
`U ⟶ S`, and `u : ℕ → U` is a family of finite type points with no
specializations `Specializes (u n) (u m)` for `n ≠ m` at which `x` is not
versal, then there is an infinite chain `x ⟶ xseq 0 ⟶ xseq 1 ⟶ ⋯` in `X`
lying over `U ⟶ Useq 0 ⟶ Useq 1 ⟶ ⋯` over `S` such that each composite
`iU n : U ⟶ Useq n` is a first-order thickening, each successive step
`step n : Useq n ⟶ Useq (n + 1)` is a first-order thickening whose kernel is
the residue-field skyscraper `κ(u (n + 1))` (source `κ(u_{n+2})`), the first
kernel of `iU 0` is `κ(u 0)` (with source `U_0 = U` as the domain of `iU 0`),
and no stage admits a local retraction of `x ⟶ xseq n` back to `x`.

The source indexing `n ≥ 1` is rendered 0-based: `u n` is source `u_{n+1}`,
`Useq n` is source `U_{n+1}`, and `iU n` is the composite `U ⟶ U_{n+1}`. -/
@[stacks 0G2S]
theorem exists_firstOrderThickeningSequence_of_not_isVersalAt
    {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    [HasStrongRimSchlessinger X] {U : Scheme.{u}} [IsAffine U]
    (hU : U ⟶ S) [LocallyOfFiniteType hU] (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u : ℕ → U)
    (hu : ∀ n, IsFiniteTypePoint (u n))
    (hns : ∀ ⦃n m⦄, n ≠ m → ¬ Specializes (u n) (u m))
    (h : ∀ n, ¬ IsVersalAt hU x hx (u n)) :
    ∃ (Useq : ℕ → Scheme.{u}) (hUseq : ∀ n, Useq n ⟶ S)
      (iU : ∀ n, U ⟶ Useq n) (hiU : ∀ n, iU n ≫ hUseq n = hU)
      (step : ∀ n, Useq n ⟶ Useq (n + 1))
      (hstep : ∀ n, step n ≫ hUseq (n + 1) = hUseq n)
      (h_comp : ∀ n, iU (n + 1) = iU n ≫ step n)
      (xseq : ℕ → X.total)
      (hxseq : ∀ n, X.p.obj (xseq n) = Over.mk (hUseq n))
      (Φ : ∀ n, x ⟶ xseq n) (φ : ∀ n, xseq n ⟶ xseq (n + 1)),
      (∀ n, X.p.IsHomLift (overHom (iU n) (hiU n)) (Φ n)) ∧
        (∀ n, X.p.IsHomLift (overHom (step n) (hstep n)) (φ n)) ∧
          (∀ n, Φ (n + 1) = Φ n ≫ φ n) ∧
            (∀ n, IsFirstOrderThickening (iU n)) ∧
              isResidueFieldKernel (iU 0) (u 0) ∧
                (∀ n, IsFirstOrderThickening (step n)) ∧
                  (∀ n, isResidueFieldKernel (step n) ((iU n).base (u (n + 1)))) ∧
                    ∀ n, ¬ existsLocalRetraction (hiU n) hx (hxseq n) (Φ n) (u n) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
