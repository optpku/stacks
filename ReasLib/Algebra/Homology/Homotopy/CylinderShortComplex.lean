/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.Homotopy.Cylinder
public import ReasLib.Algebra.Homology.Homotopy.CofiberShortComplex
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 01A3

# The degreewise split short complex of a chain-complex cylinder

The cylinder of a chain complex fits into a canonical degreewise split short complex
`A ⊞ A ⟶ A.cylinder ⟶ A⟦-1⟧`. This file exposes its structure maps, chosen splitting, and
connecting map. The universal property belongs to the generic `ShortComplex.DegreewiseSplitting`
API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

noncomputable section

universe v u

namespace ChainComplex.cylinder

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

/-- The canonical inclusion `A ⊞ A ⟶ A.cylinder`. -/
@[stacks 01A3 "cylinder short-complex inclusion"]
def inclusion (A : ChainComplex C ℤ) : A ⊞ A ⟶ A.cylinder :=
  homotopyCofiber.inclusion (biprod.lift (𝟙 A) (-𝟙 A))

/-- The degree-`n` component of the canonical projection `A.cylinder ⟶ A⟦-1⟧`. -/
@[stacks 01A3 "cylinder short-complex projection component"]
def projectionApp (A : ChainComplex C ℤ) (n : ℤ) :
    A.cylinder.X n ⟶ (A⟦(-1 : ℤ)⟧).X n :=
  homotopyCofiber.projectionApp (biprod.lift (𝟙 A) (-𝟙 A)) n

/-- The components of the cylinder projection commute with the chain differentials. -/
@[stacks 01A3 "cylinder short-complex projection naturality"]
theorem projectionApp_comm (A : ChainComplex C ℤ) (i j : ℤ)
    (hij : (ComplexShape.down ℤ).Rel i j) :
    projectionApp A i ≫ (A⟦(-1 : ℤ)⟧).d i j =
      A.cylinder.d i j ≫ projectionApp A j := sorry

/-- The canonical projection `A.cylinder ⟶ A⟦-1⟧`. -/
@[stacks 01A3 "cylinder short-complex projection"]
def projection (A : ChainComplex C ℤ) : A.cylinder ⟶ A⟦(-1 : ℤ)⟧ where
  f := (homotopyCofiber.projection (biprod.lift (𝟙 A) (-𝟙 A))).f
  comm' := (homotopyCofiber.projection (biprod.lift (𝟙 A) (-𝟙 A))).comm'

/-- The degree components of the bundled cylinder projection are `projectionApp`. -/
@[simp, stacks 01A3 "cylinder short-complex projection component formula"]
theorem projection_f (A : ChainComplex C ℤ) (n : ℤ) :
    (projection A).f n = projectionApp A n := sorry

/-- The composite of the cylinder inclusion and projection is zero. -/
@[stacks 01A3 "cylinder inclusion-projection zero law"]
theorem inclusion_comp_projection (A : ChainComplex C ℤ) :
    inclusion A ≫ projection A = 0 := sorry

/-- The canonical short complex `A ⊞ A ⟶ A.cylinder ⟶ A⟦-1⟧`. -/
@[stacks 01A3 "cylinder short complex"]
def shortComplex (A : ChainComplex C ℤ) : ShortComplex (ChainComplex C ℤ) :=
  homotopyCofiber.shortComplex (biprod.lift (𝟙 A) (-𝟙 A))

/-- The first map of the cylinder short complex is its canonical inclusion. -/
@[simp, stacks 01A3 "cylinder short-complex first map formula"]
theorem shortComplex_f (A : ChainComplex C ℤ) :
    (shortComplex A).f = inclusion A := sorry

/-- The second map of the cylinder short complex is its canonical projection. -/
@[simp, stacks 01A3 "cylinder short-complex second map formula"]
theorem shortComplex_g (A : ChainComplex C ℤ) :
    (shortComplex A).g = projection A := sorry

/-- The retraction of the cylinder inclusion in degree `n`. -/
@[stacks 01A3 "cylinder short-complex retraction component"]
def retractionApp (A : ChainComplex C ℤ) (n : ℤ) :
    A.cylinder.X n ⟶ (A ⊞ A).X n :=
  homotopyCofiber.retractionApp (biprod.lift (𝟙 A) (-𝟙 A)) n

/-- The section of the cylinder projection in degree `n`. -/
@[stacks 01A3 "cylinder short-complex section component"]
def sectionApp (A : ChainComplex C ℤ) (n : ℤ) :
    (A⟦(-1 : ℤ)⟧).X n ⟶ A.cylinder.X n :=
  homotopyCofiber.sectionApp (biprod.lift (𝟙 A) (-𝟙 A)) n

/-- The degreewise cylinder inclusion followed by its retraction is the identity. -/
@[stacks 01A3 "cylinder inclusion-retraction identity law"]
theorem inclusion_comp_retraction (A : ChainComplex C ℤ) (n : ℤ) :
    (inclusion A).f n ≫ retractionApp A n = 𝟙 _ := sorry

/-- The degreewise section followed by the cylinder projection is the identity. -/
@[stacks 01A3 "cylinder section-projection identity law"]
theorem section_comp_projection (A : ChainComplex C ℤ) (n : ℤ) :
    sectionApp A n ≫ (projection A).f n = 𝟙 _ := sorry

/-- The degreewise cylinder retraction and section decompose the identity. -/
@[stacks 01A3 "cylinder splitting identity decomposition"]
theorem splitting_id (A : ChainComplex C ℤ) (n : ℤ) :
    (retractionApp A n ≫ (inclusion A).f n) +
        ((projection A).f n ≫ sectionApp A n) =
      𝟙 _ := sorry

/-- The canonical degreewise splitting of the cylinder short complex. -/
@[stacks 01A3 "degreewise cylinder splitting"]
def splitting (A : ChainComplex C ℤ) :
    ShortComplex.DegreewiseSplitting (shortComplex A) :=
  homotopyCofiber.splitting (biprod.lift (𝟙 A) (-𝟙 A))

/-- The retraction in the canonical cylinder splitting is `retractionApp`. -/
@[simp, stacks 01A3 "cylinder splitting retraction formula"]
theorem splitting_r (A : ChainComplex C ℤ) (n : ℤ) :
    (splitting A n).r = retractionApp A n := sorry

/-- The section in the canonical cylinder splitting is `sectionApp`. -/
@[simp, stacks 01A3 "cylinder splitting section formula"]
theorem splitting_s (A : ChainComplex C ℤ) (n : ℤ) :
    (splitting A n).s = sectionApp A n := sorry

/-- The connecting map of the cylinder short complex is the shifted difference map. -/
@[stacks 01A3 "boundary map of the cylinder short complex"]
theorem boundary_eq (A : ChainComplex C ℤ) :
    homOfDegreewiseSplit (shortComplex A) (splitting A) =
      (biprod.lift (𝟙 A) (-𝟙 A))⟦(-1 : ℤ)⟧' := sorry

end ChainComplex.cylinder

namespace ChainComplex.cylinder.shortComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The canonical cylinder short complex is short exact. -/
@[stacks 01A3 "cylinder short exact sequence"]
theorem shortExact (A : ChainComplex C ℤ) :
    (ChainComplex.cylinder.shortComplex A).ShortExact := sorry

end ChainComplex.cylinder.shortComplex
