/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite standard-open covers of projective spectra

This module owns finite covers of a standard open of `Proj` by standard opens
defined by homogeneous positive-degree elements.  It is independent of a
particular projective-space presentation and distinct from principal-open
covers of `PrimeSpectrum`.
-/

@[expose] public section

open scoped AlgebraicGeometry

noncomputable section

universe u v w

namespace AlgebraicGeometry.Proj

variable {A : Type u} {σ : Type v}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- A standard open cover of `D₊(f) ⊆ Proj(𝒜)` is a finite family `D₊(gᵢ)` whose
defining elements are homogeneous of positive degree and whose union is `D₊(f)`. -/
@[stacks 01M5]
structure StandardOpenCoverOf (f : A) where
  /-- A positive degree witnessing that `f` is homogeneous. -/
  fDegree : ℕ
  /-- The target element `f` is homogeneous in degree `fDegree`. -/
  fMem : f ∈ 𝒜 fDegree
  /-- The target standard open is defined by a homogeneous element of positive degree. -/
  fDegreePos : 0 < fDegree
  /-- The finite index type of the covering family. -/
  index : Type w
  /-- The covering family is finite. -/
  finiteIndex : Finite index
  /-- The degree of the `i`-th homogeneous generator in the covering. -/
  degree : index → ℕ
  /-- The `i`-th homogeneous element defining a member of the covering. -/
  generator : index → A
  /-- Each chosen generator is homogeneous in its recorded degree. -/
  generatorMem : ∀ i, generator i ∈ 𝒜 (degree i)
  /-- Each chosen generator has positive degree. -/
  degreePos : ∀ i, 0 < degree i
  /-- The corresponding standard opens cover `D₊(f)`. -/
  cover : Proj.basicOpen 𝒜 f = ⨆ i, Proj.basicOpen 𝒜 (generator i)

namespace StandardOpenCoverOf

variable {𝒜}
variable {f : A}

/-- Construct a finite standard-open cover of `D₊(f)` from explicit homogeneous
positive-degree generators and their covering equality. -/
def ofFamily (fDegree : ℕ) (fMem : f ∈ 𝒜 fDegree) (fDegreePos : 0 < fDegree)
    (index : Type w) (finiteIndex : Finite index) (degree : index → ℕ)
    (generator : index → A) (generatorMem : ∀ i, generator i ∈ 𝒜 (degree i))
    (degreePos : ∀ i, 0 < degree i)
    (cover : Proj.basicOpen 𝒜 f = ⨆ i, Proj.basicOpen 𝒜 (generator i)) :
    StandardOpenCoverOf 𝒜 f where
  fDegree := fDegree
  fMem := fMem
  fDegreePos := fDegreePos
  index := index
  finiteIndex := finiteIndex
  degree := degree
  generator := generator
  generatorMem := generatorMem
  degreePos := degreePos
  cover := cover

/-- The family of standard opens underlying a standard open cover of `D₊(f)`. -/
@[stacks 01M5 "projective standard-open cover family"]
def opens (𝒰 : StandardOpenCoverOf 𝒜 f) :
    𝒰.index → TopologicalSpace.Opens (Proj 𝒜) :=
  fun i ↦ Proj.basicOpen 𝒜 (𝒰.generator i)

/-- Evaluation of the standard-open family underlying a cover. -/
@[simp, stacks 01M5 "projective standard-open cover family evaluation"]
theorem opens_apply (𝒰 : StandardOpenCoverOf 𝒜 f) (i : 𝒰.index) :
    𝒰.opens i = Proj.basicOpen 𝒜 (𝒰.generator i) := sorry

/-- Each member of a standard open cover is defined by a homogeneous element of positive degree. -/
@[stacks 01M5 "projective standard-open generator specification"]
theorem generator_spec (𝒰 : StandardOpenCoverOf 𝒜 f) (i : 𝒰.index) :
    𝒰.generator i ∈ 𝒜 (𝒰.degree i) ∧ 0 < 𝒰.degree i := sorry

/-- The standard-open family of a cover has supremum `D₊(f)`. -/
@[stacks 01M5 "projective standard-open cover supremum"]
theorem iSup_eq (𝒰 : StandardOpenCoverOf 𝒜 f) :
    (⨆ i, 𝒰.opens i) = Proj.basicOpen 𝒜 f := sorry

/-- Each member of a standard open cover of `D₊(f)` is contained in `D₊(f)`. -/
@[stacks 01M5 "projective standard-open cover containment"]
theorem le (𝒰 : StandardOpenCoverOf 𝒜 f) (i : 𝒰.index) :
    𝒰.opens i ≤ Proj.basicOpen 𝒜 f := sorry

/-- The target and every generator are homogeneous of positive degree, and the corresponding
standard opens cover the target standard open. -/
@[stacks 01M5]
theorem spec (𝒰 : StandardOpenCoverOf 𝒜 f) :
    (f ∈ 𝒜 𝒰.fDegree ∧ 0 < 𝒰.fDegree) ∧
      (∀ i : 𝒰.index, 𝒰.generator i ∈ 𝒜 (𝒰.degree i) ∧ 0 < 𝒰.degree i) ∧
      Proj.basicOpen 𝒜 f = ⨆ i : 𝒰.index, Proj.basicOpen 𝒜 (𝒰.generator i) := sorry

end StandardOpenCoverOf

end AlgebraicGeometry.Proj
