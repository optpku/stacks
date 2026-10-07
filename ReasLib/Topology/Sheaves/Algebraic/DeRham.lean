module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DeRham
public import ReasLib.Topology.Sheaves.Ring.Definition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative de Rham complexes on a topological space

This file specializes the arbitrary ringed-site construction to morphisms of commutative ring
sheaves on one topological space.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf.DeRham

variable {X : TopCat.{u}} {O₁ O₂ : X.Sheaf CommRingCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat]

/-- The sheaf of relative differential `p`-forms for a morphism of commutative ring sheaves on a
topological space. -/
@[stacks 0FKM]
abbrev form (φ : O₁ ⟶ O₂) (p : ℕ) :
    SheafOfModules (TopCat.Sheaf.ringSheafOfComm O₂) :=
  SheafOfModules.RingedSite.DeRham.form
    (J := Opens.grothendieckTopology X) φ p

/-- Relative differential `p`-forms, regarded as modules over the source ring sheaf. -/
@[stacks 0FKM "scalar-restricted term"]
abbrev term (φ : O₁ ⟶ O₂) (p : ℕ) :
    SheafOfModules (TopCat.Sheaf.ringSheafOfComm O₁) :=
  SheafOfModules.RingedSite.DeRham.term
    (J := Opens.grothendieckTopology X) φ p

/-- A local basic form `b₀ db₁ ∧ ... ∧ dbₚ`. -/
@[stacks 0FKN "basic form"]
abbrev basic (φ : O₁ ⟶ O₂) (p : ℕ) (U : (Opens X)ᵒᵖ)
    (b₀ : O₂.obj.obj U) (bs : Fin p → O₂.obj.obj U) : (term φ p).val.obj U :=
  SheafOfModules.RingedSite.DeRham.basic
    (J := Opens.grothendieckTopology X) φ p U b₀ bs

/-- The degree-raising differential on relative forms. -/
@[stacks 0FKM]
abbrev d (φ : O₁ ⟶ O₂) (p : ℕ) : term φ p ⟶ term φ (p + 1) :=
  SheafOfModules.RingedSite.DeRham.d
    (J := Opens.grothendieckTopology X) φ p

/-- Consecutive topological-space de Rham differentials compose to zero. -/
@[stacks 0FKM "differential squares to zero"]
theorem d_sq (φ : O₁ ⟶ O₂) (p : ℕ) :
    d φ p ≫ d φ (p + 1) = 0 := sorry

/-- Definition 17.30.1 (0FKM): the relative de Rham complex of a morphism of commutative ring
sheaves on a topological space. -/
@[stacks 0FKM]
abbrev complex (φ : O₁ ⟶ O₂) :
    CochainComplex (SheafOfModules (TopCat.Sheaf.ringSheafOfComm O₁)) ℕ :=
  SheafOfModules.RingedSite.DeRham.complex
    (J := Opens.grothendieckTopology X) φ

/-- The degree-`p` object of the relative de Rham complex is its scalar-restricted form sheaf. -/
@[stacks 0FKM "term component"]
theorem complex_X (φ : O₁ ⟶ O₂) (p : ℕ) :
    (complex φ).X p = term φ p := sorry

/-- The consecutive-degree map of the relative de Rham complex is its degree-`p`
differential. -/
@[stacks 0FKM "differential component"]
theorem complex_d (φ : O₁ ⟶ O₂) (p : ℕ) :
    (complex φ).d p (p + 1) = d φ p := sorry

/-- Equation 17.30.1.1 (0FKN): the differential sends a local basic form
`b₀ db₁ ∧ ... ∧ dbₚ` to `db₀ ∧ db₁ ∧ ... ∧ dbₚ`. -/
@[stacks 0FKN]
theorem d_basic (φ : O₁ ⟶ O₂) (p : ℕ) (U : (Opens X)ᵒᵖ)
    (b₀ : O₂.obj.obj U) (bs : Fin p → O₂.obj.obj U) :
    (d φ p).val.app U (basic φ p U b₀ bs) =
      basic φ (p + 1) U 1 (Fin.cons b₀ bs) := sorry

end TopCat.Sheaf.DeRham
