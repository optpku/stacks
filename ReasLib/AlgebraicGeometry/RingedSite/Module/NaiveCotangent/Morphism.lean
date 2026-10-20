/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent
public import ReasLib.AlgebraicGeometry.RingedSite.CommRing.Pullback
import Mathlib.Tactic.CrossRefAttribute

/-!
# Naive cotangent complexes of morphisms of ringed sites

This leaf specializes the site-level two-term complex to a bundled morphism
between commutative ringed-site presentations.  Downstream users only supply
the morphism; its continuous base functor, inverse-image structure sheaf, and
adjoint structure map are recovered from the bundled API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace RingedSite.Hom

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf JC CommRingCat.{u}} {𝒪' : Sheaf JD CommRingCat.{u}}

/-- The commutative-ring morphism `f⁻¹𝒪_Y ⟶ 𝒪_X`, regarded as the canonical
`Under`-object over the inverse-image structure sheaf. -/
@[stacks 08U0 "structure-sheaf map"]
abbrev structureSheafUnder
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪')) :
    Under (inverseImageStructureSheaf f) :=
  Under.mk (inverseImageStructureSheafMap f)

/-- Definition 18.35.4 (08U0): the naive cotangent complex of a morphism of
commutative ringed-site presentations is `NL(𝒪_X / f⁻¹𝒪_Y)`. -/
@[stacks 08U0]
noncomputable abbrev naiveCotangent
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪')) :
    CochainComplex (SheafOfModules (ringSheaf JC 𝒪)) ℤ :=
  SheafOfModules.RingedSite.NaiveCotangent.obj
    (inverseImageStructureSheaf f) (structureSheafUnder f)

/-- Reusable notation for the naive cotangent complex of a bundled morphism of
commutative ringed sites. -/
scoped[RingedSite.Hom] notation:max "NL[" f "]" =>
  RingedSite.Hom.naiveCotangent f

open scoped RingedSite.Hom

/-- The degree `-1` term of the naive cotangent complex is the conormal sheaf of
the canonical polynomial presentation. -/
theorem naiveCotangent_X_negOne
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪')) :
    (NL[f]).X (-1) =
      conormalSource
        (FreeAlgebra.Presentation.map (inverseImageStructureSheaf f)
          (structureSheafUnder f)) := sorry

/-- The degree `0` term of the naive cotangent complex is the differential
module of the canonical polynomial presentation, extended to `𝒪_X`. -/
theorem naiveCotangent_X_zero
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪')) :
    (NL[f]).X 0 =
      conormalTensorTerm
        (FreeAlgebra.Presentation.base (inverseImageStructureSheaf f)
          (structureSheafUnder f))
        (FreeAlgebra.Presentation.map (inverseImageStructureSheaf f)
          (structureSheafUnder f)) := sorry

/-- The only nonzero differential of the naive cotangent complex is the
conormal map of the canonical polynomial presentation. -/
theorem naiveCotangent_d_negOne_zero
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪')) :
    (NL[f]).d (-1) 0 =
      conormalMap
        (FreeAlgebra.Presentation.base (inverseImageStructureSheaf f)
          (structureSheafUnder f))
        (FreeAlgebra.Presentation.map (inverseImageStructureSheaf f)
          (structureSheafUnder f)) := sorry

end RingedSite.Hom

-- Both data declarations are canonical compositions of the inverse-image
-- structure-sheaf API and the site-level naive cotangent construction.  The
-- complex audit may inherit `sorryAx` only through Prop-valued complex laws in
-- the existing site-level owner; its terms and differential are explicit.
