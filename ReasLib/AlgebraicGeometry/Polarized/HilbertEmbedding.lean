/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Relative.TwistCohomology
public import ReasLib.AlgebraicGeometry.Scheme.Module.HilbertPolynomial
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Yoneda.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Fiber
public import ReasLib.RingTheory.Polynomial.Numerical
public import ReasLib.Topology.Noetherian.Basic
public import ReasLib.AlgebraicGeometry.Polarized.AlgebraicStack
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Topology

/-!
# Hilbert-embedded polarized schemes

Field-valued representatives with fixed Hilbert polynomial and projective
embedding dimension define a locus whose subsets are Noetherian and quasi-compact.
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
  Scheme.Hom.HasHilbertPolynomial
      ((polarizedObj p).hom ≫ eqToHom (polarizedObj_S p))
      (polarizedObj p).line P ∧
    isProjectivelyEmbedded (polarizedObj p) n

/-- Hilbert-embeddedness is the conjunction of the Hilbert-polynomial identity
for the polarized structure morphism via `polarizedObj_S` and the projective
embedding over the base. -/
theorem IsHilbertEmbedded_iff (n : ℕ) (P : ℤ → ℤ)
    (p : FieldValuedPoint toGroupoidsOverSpecZ) :
    IsHilbertEmbedded n P p ↔
      Scheme.Hom.HasHilbertPolynomial
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

/-- A subset of the point space of polarized proper schemes is Noetherian if
its points admit field-valued representatives with a fixed numerical Hilbert
polynomial and a closed embedding into a fixed positive-dimensional projective
space pulling back the twisting sheaf to the polarization. -/
@[stacks 0E96]
theorem noetherianSpace_hilbertEmbedded {n : ℕ} (hn : 1 ≤ n) {P : ℤ → ℤ}
    (hP : IsNumericalPolynomial P) (T : Set (Points toGroupoidsOverSpecZ))
    (hT : T ⊆ hilbertEmbeddedSet n P) :
    TopologicalSpace.NoetherianSpace T :=
  sorry

/-- A subset of the point space of polarized proper schemes is quasi-compact if
its points admit field-valued representatives with a fixed numerical Hilbert
polynomial and a closed embedding into a fixed positive-dimensional projective
space pulling back the twisting sheaf to the polarization. -/
@[stacks 0E96]
theorem isCompact_hilbertEmbedded {n : ℕ} (hn : 1 ≤ n) {P : ℤ → ℤ}
    (hP : IsNumericalPolynomial P) (T : Set (Points toGroupoidsOverSpecZ))
    (hT : T ⊆ hilbertEmbeddedSet n P) :
    CompactSpace T :=
  sorry

end AlgebraicGeometry.Polarized
