/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.Topology.Sheaves.Algebraic.DeRham
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative de Rham complexes on ringed spaces

The construction is owned on arbitrary ringed sites.  This file supplies the concise ringed-space
specialization and notation whose owner does not depend on a textbook chapter.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.DeRham

variable {X S : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat]

/-- The inverse-image coefficient sheaf `f⁻¹𝒪_S` of a morphism of ringed spaces. -/
abbrev coefficients (f : X ⟶ S) : TopCat.Sheaf CommRingCat.{u} X :=
  (TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj S.sheaf

/-- Modules over the inverse-image coefficient sheaf `f⁻¹𝒪_S`. -/
abbrev Modules (f : X ⟶ S) := SheafOfModules (TopCat.Sheaf.ringSheafOfComm (coefficients f))

/-- The morphism `f⁻¹𝒪_S ⟶ 𝒪_X` defining relative differential forms. -/
abbrev structureMap (f : X ⟶ S) : coefficients f ⟶ X.sheaf :=
  RingedSpace.Hom.inverseImageStructureSheafHomComm f

/-- The sheaf `Ω^p_{X/S}` with its natural `𝒪_X`-module structure. -/
@[stacks 0FKQ "(1)"]
abbrev form (f : X ⟶ S) (p : ℕ) : X.Modules :=
  TopCat.Sheaf.DeRham.form (structureMap f) p

/-- The degree-`p` relative de Rham term, regarded as an `f⁻¹𝒪_S`-module. -/
@[stacks 0FKQ "(1), scalar-restricted term"]
abbrev term (f : X ⟶ S) (p : ℕ) : Modules f :=
  TopCat.Sheaf.DeRham.term (structureMap f) p

/-- The relative de Rham differential in degree `p`. -/
@[stacks 0FKQ "(1), differential"]
abbrev d (f : X ⟶ S) (p : ℕ) : term f p ⟶ term f (p + 1) :=
  TopCat.Sheaf.DeRham.d (structureMap f) p

/-- Consecutive relative de Rham differentials on a ringed space compose to zero. -/
@[stacks 0FKQ "differential squares to zero"]
theorem d_sq (f : X ⟶ S) (p : ℕ) :
    d f p ≫ d f (p + 1) = 0 := sorry

/-- Definition 17.30.4 (0FKQ) (1): the relative de Rham complex `Ω^•_{X/S}` of a morphism of
ringed spaces. -/
@[stacks 0FKQ "(1)"]
abbrev complex (f : X ⟶ S) : CochainComplex (Modules f) ℕ :=
  TopCat.Sheaf.DeRham.complex (structureMap f)

/-- The degree-`p` object of `Ω^•_{X/S}` is the relative form sheaf with scalars restricted to
`f⁻¹𝒪_S`. -/
@[stacks 0FKQ "(1), term component"]
theorem complex_X (f : X ⟶ S) (p : ℕ) :
    (complex f).X p = term f p := sorry

/-- The consecutive-degree map of `Ω^•_{X/S}` is the relative de Rham differential in degree
`p`. -/
@[stacks 0FKQ "(1), differential component"]
theorem complex_d (f : X ⟶ S) (p : ℕ) :
    (complex f).d p (p + 1) = d f p := sorry

end AlgebraicGeometry.RingedSpace.DeRham

namespace AlgebraicGeometry

/-- The relative de Rham complex of a morphism of ringed spaces. -/
scoped[AlgebraicGeometry] notation:max "Ωᵈᴿ[" f "]" => RingedSpace.DeRham.complex f

/-- Relative differential `p`-forms of a morphism of ringed spaces. -/
scoped[AlgebraicGeometry] notation:max "Ωᵈᴿ[" p "][" f "]" => RingedSpace.DeRham.form f p

end AlgebraicGeometry
