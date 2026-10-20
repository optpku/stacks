module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import ReasLib.FieldTheory.Galois.KrullTopology

@[expose] public section

universe u v

namespace GroupCohomology

variable {G : Type u} {A : Type v} [Group G] [Group A] [MulDistribMulAction G A]

open scoped MatrixGroups

/-- Multiplicative 1-cocycles for an action of `G` on the group `A`. -/
def NonabelianCocycle : Type (max u v) :=
  {c : G → A // ∀ σ τ, c (σ * τ) = c σ * σ • c τ}

/-- The standard cohomology relation between multiplicative 1-cocycles. -/
def NonabelianCohomologous (c₁ c₂ : NonabelianCocycle (G := G) (A := A)) : Prop :=
  ∃ a : A, ∀ σ : G, c₂.1 σ = a⁻¹ * c₁.1 σ * σ • a

/-- The non-abelian cohomology relation is an equivalence relation. -/
theorem nonabelianCohomologous_equivalence :
    Equivalence (NonabelianCohomologous (G := G) (A := A)) := sorry

/-- The quotient of multiplicative 1-cocycles by cohomology. -/
def nonabelianH1 : Type (max u v) :=
  Quotient (⟨NonabelianCohomologous (G := G) (A := A),
    nonabelianCohomologous_equivalence (G := G) (A := A)⟩ :
      Setoid (NonabelianCocycle (G := G) (A := A)))

/-- The cohomology class represented by a multiplicative 1-cocycle. -/
def NonabelianCocycle.class (c : NonabelianCocycle (G := G) (A := A)) :
    nonabelianH1 (G := G) (A := A) := Quotient.mk _ c

/-- Equality of non-abelian cohomology classes is cohomology equivalence. -/
theorem NonabelianCocycle.class_eq_iff
    (c₁ c₂ : NonabelianCocycle (G := G) (A := A)) :
    c₁.class = c₂.class ↔ NonabelianCohomologous c₁ c₂ := sorry

end GroupCohomology

namespace GroupCohomology

variable {G : Type u} {A : Type v} [Group G] [Group A] [MulDistribMulAction G A]
  [TopologicalSpace G]

open scoped MatrixGroups

/-- Continuity of a cocycle to the discrete coefficient group, expressed by open preimages. -/
def NonabelianCocycle.IsContinuous
    (c : NonabelianCocycle (G := G) (A := A)) : Prop :=
  ∀ U : Set A, IsOpen (c.1 ⁻¹' U)

/-- Multiplicative 1-cocycles continuous from the source topology into discrete coefficients. -/
def ContinuousNonabelianCocycle : Type (max u v) :=
  {c : NonabelianCocycle (G := G) (A := A) // c.IsContinuous}

/-- A continuous cocycle carries the corresponding discrete-continuity property. -/
theorem ContinuousNonabelianCocycle.isContinuous
    (c : ContinuousNonabelianCocycle (G := G) (A := A)) : c.1.IsContinuous := sorry

/-- The cohomology relation restricted to continuous non-abelian cocycles. -/
def ContinuousNonabelianCohomologous
    (c₁ c₂ : ContinuousNonabelianCocycle (G := G) (A := A)) : Prop :=
  NonabelianCohomologous c₁.1 c₂.1

/-- The continuous non-abelian cohomology relation is an equivalence relation. -/
theorem continuousNonabelianCohomologous_equivalence :
    Equivalence (ContinuousNonabelianCohomologous (G := G) (A := A)) := sorry

/-- Continuous non-abelian `H¹`, obtained by quotienting continuous cocycles by cohomology. -/
def continuousNonabelianH1 : Type (max u v) :=
  Quotient (⟨ContinuousNonabelianCohomologous (G := G) (A := A),
    continuousNonabelianCohomologous_equivalence (G := G) (A := A)⟩ :
      Setoid (ContinuousNonabelianCocycle (G := G) (A := A)))

/-- The continuous non-abelian cohomology class represented by a cocycle. -/
def ContinuousNonabelianCocycle.class
    (c : ContinuousNonabelianCocycle (G := G) (A := A)) :
    continuousNonabelianH1 (G := G) (A := A) := Quotient.mk _ c

/-- Equality of continuous non-abelian cohomology classes is cohomology equivalence. -/
theorem ContinuousNonabelianCocycle.class_eq_iff
    (c₁ c₂ : ContinuousNonabelianCocycle (G := G) (A := A)) :
    c₁.class = c₂.class ↔ ContinuousNonabelianCohomologous c₁ c₂ := sorry

/-- The canonical entrywise action on `PGL(d, Ksep)` induced by field automorphisms. -/
instance galoisPGLAction
    {Ksep : Type v} [Field Ksep]
    {d : ℕ} [MulSemiringAction G Ksep] :
    MulDistribMulAction G (PGL(d, Ksep)) where
  smul σ A := Matrix.ProjGenLinGroup.map (MulSemiringAction.toRingHom G Ksep σ) A
  one_smul := sorry
  mul_smul := sorry
  smul_one := sorry
  smul_mul := sorry

end GroupCohomology

end
