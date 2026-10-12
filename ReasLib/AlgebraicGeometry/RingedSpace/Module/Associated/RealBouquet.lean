/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.ContinuousMap.Lattice
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Coproduct.Sections
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Sections
public import ReasLib.AlgebraicGeometry.RingedSpace.ContinuousFunctions.Real.Bouquet
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Presentation
import Mathlib.Tactic.CrossRefAttribute

/-!
# The real-bouquet counterexample for associated module sheaves

This file owns the explicit morphism between countably generated free associated module
sheaves which is not induced by a module homomorphism on any neighborhood of the bouquet
origin.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry Topology

noncomputable section

namespace AlgebraicGeometry.RingedSpace.Module.Associated.RealBouquet

/-- The countable bouquet of real lines with uniform metric neighborhoods at the common
origin. -/
@[stacks 01BL "countable real bouquet"]
abbrev Space : TopCat :=
  TopCat.of (Metric.RealBouquet ℕ)

/- The uniform standard neighborhoods form a basis at the common origin. -/

/-- The real bouquet equipped with its sheaf of continuous real-valued functions. -/
@[stacks 01BL "continuous-function ringed space"]
noncomputable abbrev ringedSpace : RingedSpace :=
  RingedSpace.ContinuousFunctions.Real.ringedSpace Space

/-- The common origin as a point of the continuous-function ringed space. -/
@[stacks 01BL "ringed-space origin"]
noncomputable def origin : ringedSpace :=
  Metric.RealBouquet.origin

/-- The continuous cutoff function used in the real-bouquet counterexample. -/
@[stacks 01BL "cutoff function"]
noncomputable def cutoff : C(ℝ, ℝ) :=
  (1 : C(ℝ, ℝ)) ⊓ (0 ⊔ (|ContinuousMap.id ℝ| - 1))

/-- The cutoff is zero for `|x| ≤ 1`, linear for `1 ≤ |x| ≤ 2`, and one for
`2 ≤ |x|`. -/
@[simp]
theorem cutoff_apply (x : ℝ) :
    cutoff x = min 1 (max 0 (|x| - 1)) := sorry

/-- The cutoff vanishes on the interval `(-1, 1)`. -/
theorem cutoff_eq_zero {x : ℝ} (hx : |x| < 1) :
    cutoff x = 0 := sorry

/-- The cutoff equals one outside `[-2, 2]`. -/
theorem cutoff_eq_one {x : ℝ} (hx : 2 < |x|) :
    cutoff x = 1 := sorry

/-- The scaled cutoff `x ↦ cutoff ((j + 1) * x)` on the real line. -/
@[stacks 01BL "scaled cutoff"]
noncomputable def scaledCutoff (j : ℕ) : C(ℝ, ℝ) :=
  cutoff.comp
    (ContinuousMap.const ℝ (j + 1 : ℝ) * ContinuousMap.id ℝ)

/-- Evaluation of the scaled cutoff has the expected formula. -/
theorem scaledCutoff_apply (j : ℕ) (x : ℝ) :
    scaledCutoff j x = cutoff ((j + 1 : ℝ) * x) := sorry

/-- The scaled cutoff vanishes on the uniform interval of radius `(j + 1)⁻¹`. -/
theorem scaledCutoff_eq_zero {j : ℕ} {x : ℝ}
    (hx : |x| < ((j + 1 : ℕ) : ℝ)⁻¹) :
    scaledCutoff j x = 0 := sorry

/-- A branch coefficient as a global section of the structure module. -/
@[stacks 01BL "branch coefficient"]
noncomputable def branchCoefficient (j i : ℕ) :
    (SheafOfModules.unit ringedSpace.ringCatSheaf).sections :=
  RingedSpace.ContinuousFunctions.Real.Bouquet.supportedSection i (scaledCutoff j)

/-- For fixed `j`, the branch coefficients form a locally finite family of sheaf sections. -/
theorem locallyFinite_branchCoefficient (j : ℕ) :
    LocallyFinite fun i ↦ SheafOfModules.sectionSupport (branchCoefficient j i) := sorry

/-- The locally finite row `∑ i, f_j 1_{L_i} e_i` as a section of the countable free
sheaf. -/
@[stacks 01BL "locally finite row"]
noncomputable def rowSection (j : ℕ) :
    (SheafOfModules.free ℕ : ringedSpace.Modules).sections :=
  SheafOfModules.Free.sectionOfLocallyFinite
    (branchCoefficient j) (locallyFinite_branchCoefficient j)

/-- The row section embedded into the target basis by `i ↦ (j, i)`. -/
@[stacks 01BL "target row"]
noncomputable def targetRow (j : ℕ) :
    (SheafOfModules.free (ℕ × ℕ) : ringedSpace.Modules).sections :=
  SheafOfModules.sectionsMap
    (SheafOfModules.freeMap (R := ringedSpace.ringCatSheaf) fun i ↦ (j, i))
    (rowSection j)

namespace targetRow

/-- The `(j, i)` coordinate of `targetRow j` is the coefficient on branch `i`. -/
@[stacks 01BL "target coefficient"]
theorem project_same (j i : ℕ) :
    SheafOfModules.sectionsMap
        (SheafOfModules.Free.projection (𝒪 := ringedSpace.ringCatSheaf) (j, i))
        (targetRow j) =
      branchCoefficient j i := sorry

/-- Every target coordinate whose first index differs from `j` vanishes on `targetRow j`. -/
theorem project_ne {j k : ℕ} (hjk : j ≠ k) (i : ℕ) :
    SheafOfModules.sectionsMap
        (SheafOfModules.Free.projection (𝒪 := ringedSpace.ringCatSheaf) (k, i))
        (targetRow j) =
      0 := sorry

end targetRow

/-- The explicit morphism `e_j ↦ ∑ i, f_j 1_{L_i} e_(j,i)` between free module
sheaves. -/
@[stacks 01BL "counterexample morphism"]
noncomputable def freeSheafMap :
    (SheafOfModules.free ℕ : ringedSpace.Modules) ⟶
      SheafOfModules.free (ℕ × ℕ) :=
  (SheafOfModules.freeHomEquiv
    (SheafOfModules.free (ℕ × ℕ) : ringedSpace.Modules)).symm targetRow

/-- Evaluating the explicit free-sheaf morphism on `e_j` gives `targetRow j`. -/
theorem freeSheafMap_row (j : ℕ) :
    SheafOfModules.freeHomEquiv
        (SheafOfModules.free (ℕ × ℕ) : ringedSpace.Modules) freeSheafMap j =
      targetRow j := sorry

/-- The free global-sections module indexing the source associated sheaf. -/
@[stacks 01BL "source free module"]
abbrev SourceModule : ModuleCat ringedSpace.globalSectionsRing :=
  (ModuleCat.free ringedSpace.globalSectionsRing).obj ℕ

/-- The free global-sections module indexing the target associated sheaf. -/
@[stacks 01BL "target free module"]
abbrev TargetModule : ModuleCat ringedSpace.globalSectionsRing :=
  (ModuleCat.free ringedSpace.globalSectionsRing).obj (ℕ × ℕ)

/-- The explicit free-sheaf morphism transported to the corresponding associated free
modules. -/
@[stacks 01BL "associated counterexample morphism"]
noncomputable def associatedMap :
    RingedSpace.Module.Associated.obj (X := ringedSpace)
        (RingHom.id ringedSpace.globalSectionsRing) SourceModule ⟶
      RingedSpace.Module.Associated.obj (X := ringedSpace)
        (RingHom.id ringedSpace.globalSectionsRing) TargetModule :=
  RingedSpace.Module.Associated.Presentation.toAssociated
    (RingHom.id ringedSpace.globalSectionsRing) freeSheafMap

/-- On every standard uniform neighborhood, the counterexample morphism is not induced by a
homomorphism of modules over the ring of sections. -/
@[stacks 01BL "standard-neighborhood obstruction"]
theorem not_isInducedOn_standardNeighborhood (n : ℕ) :
    ¬ RingedSpace.Module.Associated.Morphism.IsInducedOn
      (RingHom.id ringedSpace.globalSectionsRing) associatedMap
        (Metric.RealBouquet.standardNeighborhood n) := sorry

/-- Example 17.10.9 (01BL): the explicit morphism
`e_j ↦ ∑ i, f_j 1_{L_i} e_(j,i)` between associated free module sheaves is not induced
by a module homomorphism on any neighborhood of the common origin. -/
@[stacks 01BL "not locally induced"]
theorem not_isLocallyInducedAt :
    ¬ RingedSpace.Module.Associated.Morphism.IsLocallyInducedAt
      (RingHom.id ringedSpace.globalSectionsRing) associatedMap origin := sorry

end AlgebraicGeometry.RingedSpace.Module.Associated.RealBouquet
