/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Homology
import StacksCheckRecall

/-!
# Lemma 24.26.2

Acyclic objects are modeled by the homological kernel of DG cohomology.  Its closure properties
are reusable object-property instances rather than a chapter-specific conjunction.
-/

@[expose] public section

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}} (𝒜 : DGA(𝒪))

/- Lemma 24.26.2 (1) (0FT3): acyclic objects are closed under isomorphisms. -/
@[stacks 0FT3]
#check
  (inferInstance : (Homotopy.acyclic 𝒜).IsClosedUnderIsomorphisms)

/- Lemma 24.26.2 (2) (0FT3): acyclic objects are stable under retracts. -/
@[stacks 0FT3]
#check
  (inferInstance : (Homotopy.acyclic 𝒜).IsStableUnderRetracts)

/- Lemma 24.26.2 (3) (0FT3): acyclic objects form a triangulated subcategory. -/
@[stacks 0FT3]
#check
  (inferInstance : (Homotopy.acyclic 𝒜).IsTriangulated)

end SheafOfModules.RingedSite.DifferentialGradedModule
