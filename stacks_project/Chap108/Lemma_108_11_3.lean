/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Relative.TwistCohomology
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.EulerCharacteristic
public import ReasLib.AlgebraicGeometry.Scheme.Module.TensorPower
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Yoneda.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Fiber
public import ReasLib.RingTheory.Polynomial.Numerical
public import ReasLib.Topology.Noetherian.Basic
public import stacks_project.Chap99.Theorem_99_14_15_Algebraicity_of_the_stack_of_polarized_schemes
public import stacks_project.Chap100.Definition_100_4_2_Points
public import stacks_project.Chap101.Definition_101_13_2_Closed

/-!
# Lemma 108.11.3

A subset of `|Polarized|` whose points are represented by polarized pairs of
Hilbert polynomial `P` that embed as closed subschemes of `P^n` over a field is
Noetherian, hence quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open FiberedCategoryOver.Groupoids BasedCategory.Yoneda.Identity
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

/-- The polarized object `(X, L)` represented by a field-valued point of
`Polarized`. -/
def polarizedObj (p : FieldValuedPoint toGroupoidsOverSpecZ) : Obj :=
  ((fiberFunctor p.hom p.overObj).obj (fiberObj p.overObj)).1

/-- The base of `polarizedObj p` is the spectrum of the source field of `p`. -/
theorem polarizedObj_S (p : FieldValuedPoint toGroupoidsOverSpecZ) :
    (polarizedObj p).S = Spec (.of p.K) :=
  sorry

/-- A scheme proper over the spectrum of a field is locally Noetherian. -/
theorem isLocallyNoetherian_of_isProper_over_field
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] : IsLocallyNoetherian X :=
  sorry

/-- Integral tensor powers of an invertible module on a locally Noetherian
scheme are coherent, so that the Euler characteristic of `L^{⊗ t}` is defined.
This reuses `Scheme.Modules.instIsCoherentOfIsInvertible` at the locally
Noetherian layer rather than claiming coherence on every scheme. -/
instance instIsCoherent_tensorPowerInt {X : Scheme.{u}} [IsLocallyNoetherian X]
    (L : X.Modules) [Scheme.Modules.Invertible L] (t : ℤ) :
    (Scheme.Modules.tensorPowerInt L t).IsCoherent :=
  sorry

/-- The Hilbert polynomial of an invertible module `L` on a scheme proper over a
field is the function `t ↦ χ(X, L^{⊗ t})`. -/
def hasHilbertPolynomial {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsLocallyNoetherian X]
    (L : X.Modules) [Scheme.Modules.Invertible L] (P : ℤ → ℤ) : Prop :=
  ∀ t : ℤ, Scheme.Hom.eulerCharacteristic f (Scheme.Modules.tensorPowerInt L t) = P t

/-- Having Hilbert polynomial `P` means `χ(X, L^{⊗ t}) = P t` for every integer
`t`. -/
theorem hasHilbertPolynomial_iff {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsLocallyNoetherian X]
    (L : X.Modules) [Scheme.Modules.Invertible L] (P : ℤ → ℤ) :
    hasHilbertPolynomial f L P ↔
      ∀ t : ℤ,
        Scheme.Hom.eulerCharacteristic f (Scheme.Modules.tensorPowerInt L t) = P t :=
  sorry

/-- The line bundle of a polarized object is invertible. -/
instance instInvertible_line (x : Obj) : Scheme.Modules.Invertible x.line :=
  x.relativelyAmple.invertible

/-- The structure morphism of a polarized object remains proper after
identifying its base with the spectrum of a field. -/
instance instIsProper_hom_overField {k : Type u} [Field k] (x : Obj)
    (hS : x.S = Spec (.of k)) : IsProper (x.hom ≫ eqToHom hS) :=
  sorry

/-- The source of a polarized object over a field is locally Noetherian. -/
instance instIsLocallyNoetherian_polarizedObj
    (p : FieldValuedPoint toGroupoidsOverSpecZ) :
    IsLocallyNoetherian (polarizedObj p).X :=
  sorry

/-- A polarized object is projectively embedded in `P^n` over its base when it
admits a closed immersion into `ProjectiveSpace n x.S` over `x.hom` pulling
`𝒪(1)` back to its line bundle. -/
def isProjectivelyEmbedded (x : Obj) (n : ℕ) : Prop :=
  ∃ i : x.X ⟶ ProjectiveSpace n x.S,
    i ≫ ProjectiveSpace.toBase n x.S = x.hom ∧
      IsClosedImmersion i ∧
        Nonempty
          ((Scheme.Modules.pullback i).obj
              (ProjectiveSpace.relativeTwistingSheaf x.S n 1) ≅ x.line)

/-- Projective embedding is the conjunction of a closed immersion into `P^n`
over the structure morphism and an isomorphism `i^* 𝒪(1) ≅ L`. -/
theorem isProjectivelyEmbedded_iff (x : Obj) (n : ℕ) :
    isProjectivelyEmbedded x n ↔
      ∃ i : x.X ⟶ ProjectiveSpace n x.S,
        i ≫ ProjectiveSpace.toBase n x.S = x.hom ∧
          IsClosedImmersion i ∧
            Nonempty
              ((Scheme.Modules.pullback i).obj
                  (ProjectiveSpace.relativeTwistingSheaf x.S n 1) ≅ x.line) :=
  sorry

/-- A field-valued point of `Polarized` is Hilbert-embedded of type `(n, P)` when
the polarized pair it represents has Hilbert polynomial `P` along the structure
morphism over its source field, and embeds as a closed subscheme of `P^n` over
that field. -/
def IsHilbertEmbedded (n : ℕ) (P : ℤ → ℤ)
    (p : FieldValuedPoint toGroupoidsOverSpecZ) : Prop :=
  hasHilbertPolynomial
      ((polarizedObj p).hom ≫ eqToHom (polarizedObj_S p))
      (polarizedObj p).line P ∧
    isProjectivelyEmbedded (polarizedObj p) n

/-- Hilbert-embeddedness is the conjunction of the Hilbert-polynomial identity
for the polarized structure morphism via `polarizedObj_S` and the projective
embedding over the base. -/
theorem IsHilbertEmbedded_iff (n : ℕ) (P : ℤ → ℤ)
    (p : FieldValuedPoint toGroupoidsOverSpecZ) :
    IsHilbertEmbedded n P p ↔
      hasHilbertPolynomial
          ((polarizedObj p).hom ≫ eqToHom (polarizedObj_S p))
          (polarizedObj p).line P ∧
        isProjectivelyEmbedded (polarizedObj p) n :=
  sorry

/-- The locus of points of `|Polarized|` that admit a Hilbert-embedded
representative of type `(n, P)`. -/
def hilbertEmbeddedSet (n : ℕ) (P : ℤ → ℤ) :
    Set (Points toGroupoidsOverSpecZ) :=
  {ξ | ∃ p, Points.mk p = ξ ∧ IsHilbertEmbedded n P p}

/-- Membership in `hilbertEmbeddedSet n P` is existence of a Hilbert-embedded
field-valued representative. -/
theorem mem_hilbertEmbeddedSet_iff (n : ℕ) (P : ℤ → ℤ)
    (ξ : Points toGroupoidsOverSpecZ) :
    ξ ∈ hilbertEmbeddedSet n P ↔
      ∃ p, Points.mk p = ξ ∧ IsHilbertEmbedded n P p :=
  sorry

/-- The subspace topology on a set of points of `|Polarized|`, induced by a
topology on the points space. -/
abbrev pointsSubtypeTopology
    (τ : TopologicalSpace (Points toGroupoidsOverSpecZ))
    (T : Set (Points toGroupoidsOverSpecZ)) : TopologicalSpace T :=
  @instTopologicalSpaceSubtype (Points toGroupoidsOverSpecZ) (fun ξ ↦ ξ ∈ T) τ

/-- Lemma 108.11.3 (1): a subset of `|Polarized|` whose points are represented by
polarized pairs of Hilbert polynomial `P` that embed as closed subschemes of
`P^n` over a field is a Noetherian topological space. -/
@[stacks 0E96]
theorem noetherianSpace_hilbertEmbedded {n : ℕ} (hn : 1 ≤ n) {P : ℤ → ℤ}
    (hP : IsNumericalPolynomial P) (T : Set (Points toGroupoidsOverSpecZ))
    (τ : TopologicalSpace (Points toGroupoidsOverSpecZ))
    (hτ : IsPointsTopology toGroupoidsOverSpecZ τ)
    (hT : T ⊆ hilbertEmbeddedSet n P) :
    @TopologicalSpace.NoetherianSpace T (pointsSubtypeTopology τ T) :=
  sorry

/-- Lemma 108.11.3 (2): in particular, such a subset is a quasi-compact
topological space. -/
@[stacks 0E96]
theorem isCompact_hilbertEmbedded {n : ℕ} (hn : 1 ≤ n) {P : ℤ → ℤ}
    (hP : IsNumericalPolynomial P) (T : Set (Points toGroupoidsOverSpecZ))
    (τ : TopologicalSpace (Points toGroupoidsOverSpecZ))
    (hτ : IsPointsTopology toGroupoidsOverSpecZ τ)
    (hT : T ⊆ hilbertEmbeddedSet n P) :
    @CompactSpace T (pointsSubtypeTopology τ T) :=
  sorry

end AlgebraicGeometry.Polarized
