/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Homology

/-!
# Acyclic differential graded modules

This leaf owns acyclicity at the represented DG-module layer.  The public predicate is stated on
the underlying cochain complex, while comparison lemmas connect it to the intrinsic homotopy
category without forcing downstream statements to expose `toK`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open DifferentialGradedCategory
open scoped DifferentialGradedCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

-- Mathlib intentionally keeps this construction non-global because a global instance breaks
-- sheaf/free elaboration.  Acyclicity is compared inside the pinned homotopy triangulation.
attribute [local instance] Abelian.hasFiniteBiproducts

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedModule.Module

section Underlying


variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- A DG module is acyclic when its underlying cochain complex is acyclic. -/
def acyclic (𝒜 : DGA(𝒪)) : ObjectProperty Mod(𝒜, d) :=
  fun M ↦ HomologicalComplex.Acyclic M.toComplex

/-- Typeclass-style membership in the acyclic DG-module object property. -/
abbrev IsAcyclic {𝒜 : DGA(𝒪)} (M : Mod(𝒜, d)) : Prop :=
  (acyclic 𝒜).Is M

namespace Acyclic

/-- Module-level acyclicity is exactly acyclicity of the underlying cochain complex. -/
theorem iff_underlying (𝒜 : DGA(𝒪)) (M : Mod(𝒜, d)) :
    acyclic 𝒜 M ↔ HomologicalComplex.Acyclic M.toComplex := sorry

end Acyclic

end Underlying

section Homotopy


variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

namespace Acyclic

/-- A represented DG module is acyclic exactly when its intrinsic homotopy object is acyclic. -/
theorem toK_obj_iff (𝒜 : DGA(𝒪)) (M : Mod(𝒜, d)) :
    acyclic 𝒜 M ↔ Homotopy.acyclic 𝒜 ((toK 𝒜).obj M) := sorry

/-- An acyclic DG module gives an acyclic object in the intrinsic homotopy category. -/
theorem homotopy_mem (𝒜 : DGA(𝒪)) (M : Mod(𝒜, d)) [IsAcyclic M] :
    Homotopy.acyclic 𝒜 ((toK 𝒜).obj M) := sorry

end Acyclic

end Homotopy


end SheafOfModules.RingedSite.DifferentialGradedModule.Module
