/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.KFlat
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Localization
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Localization
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.Tactic.CrossRefAttribute

/-!
# K-flat complexes on localized ringed sites

This leaf owns the restriction theorem at the cochain-complex level.  The restriction functor and
its complex lift are imported from their lower-level owners, so users do not need to import a
chapter file to reuse K-flatness after localization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.CochainComplex.IsKFlat

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasBinaryProducts C]
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]
variable (U : C)
variable [MonoidalCategory (SheafOfModules ((ringSheaf J 𝒪).over U))]
variable [MonoidalPreadditive (SheafOfModules ((ringSheaf J 𝒪).over U))]

/-- Lemma 21.17.4 (0E8K): restriction to a localized ringed site preserves K-flat cochain
complexes. -/
@[stacks 0E8K "localized restriction preserves K-flatness"]
theorem localizedRestriction
    (K : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ) (hK : K.IsKFlat) :
    (((SheafOfModules.RingedSite.Localization.restriction 𝒪 U).mapHomologicalComplex
      (up ℤ)).obj K).IsKFlat := sorry

end SheafOfModules.RingedSite.CochainComplex.IsKFlat
