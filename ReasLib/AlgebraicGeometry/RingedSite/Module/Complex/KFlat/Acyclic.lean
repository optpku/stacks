module

public import ReasLib.Algebra.Homology.HomologicalComplex.KFlat.Acyclic
public import ReasLib.Algebra.Homology.HomologicalComplex.Flat
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cycles of acyclic K-flat complexes on ringed sites

This file specializes the category-level cycles theorem to module sheaves on a ringed site.  It
keeps the structure sheaf visible in the conclusion while retaining the canonical
`HomologicalComplex.IsTermwiseFlat` hypothesis.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.CochainComplex.IsKFlat

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {O : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (ringedSiteModuleCategory J O)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J O)]

/-- Lemma 21.17.16 (0G7C): the cycles of an acyclic, termwise-flat K-flat complex of module
sheaves are flat. -/
@[stacks 0G7C]
theorem isFlat_cycles
    {K : CochainComplex (ringedSiteModuleCategory J O) ℤ}
    (hK : K.IsKFlat) (hAcyclic : K.Acyclic)
    (hFlat : HomologicalComplex.IsTermwiseFlat K) (n : ℤ) :
    IsFlat O (K.cycles n) := sorry

/-- The source-text kernel formulation of Lemma 21.17.16, exposed as a view of the canonical
cycles statement. -/
theorem isFlat_kernel_dFrom
    {K : CochainComplex (ringedSiteModuleCategory J O) ℤ}
    (hK : K.IsKFlat) (hAcyclic : K.Acyclic)
    (hFlat : HomologicalComplex.IsTermwiseFlat K) (n : ℤ) :
    IsFlat O (kernel (K.dFrom n)) := sorry

end SheafOfModules.RingedSite.CochainComplex.IsKFlat
