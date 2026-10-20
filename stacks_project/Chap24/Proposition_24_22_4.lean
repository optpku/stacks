/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Triangulated
import StacksCheckRecall

open CategoryTheory
open CategoryTheory.Pretriangulated
open DifferentialGradedCategory
open scoped DifferentialGradedCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedModule

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable (𝒜 : DGA(𝒪))

/- Proposition 24.22.4 (1): the intrinsic DG homotopy category is triangulated. -/
@[stacks 0FS7] #check
  (Homotopy.isTriangulated 𝒜 : IsTriangulated (K ℤ Mod(𝒜, d)))

/- Proposition 24.22.4 (2): its shift is the explicit quotient of the degreewise DG-module
shift constructed in Section 24.20. -/
@[stacks 0FS7] #check
  (Shift.K.hasShift 𝒜 : HasShift (K ℤ Mod(𝒜, d)) ℤ)
#check Shift.K.shiftFunctor_eq 𝒜

/- Proposition 24.22.4 (3): the distinguished triangles are precisely the triangles isomorphic
to canonical DG-module mapping-cone triangles. This is the intrinsic formalization of the
admissible-short-exact-sequence presentation in the source. -/
@[stacks 0FS7] #check Homotopy.distTriang_eq 𝒜
#check Homotopy.mem_distinguished 𝒜

end


end SheafOfModules.RingedSite.DifferentialGradedModule
