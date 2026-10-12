/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.AbelianDual.InjectiveTarget
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.InjectiveCoseparator
import Mathlib.Tactic.CrossRefAttribute

/-!
# Existence of injective targets for abelian duality

This leaf isolates the noncanonical existence statement used by abelian duality on a ringed site.
Consumers which already carry a target should import `AbelianDual.InjectiveTarget` instead.
The coefficient and target universes remain independent.
-/

@[expose] public section

open CategoryTheory

universe u v w z

namespace SheafOfModules.RingedSite.AbelianDual.InjectiveTarget

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose
  (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasSheafify J AddCommGrpCat.{max u v z}]

/-- A ringed site admits an injective abelian sheaf which separates maps of module sheaves. -/
@[stacks 01DQ "existence of an injective duality target"]
theorem nonempty (O : Sheaf J CommRingCat.{w}) :
    Nonempty (AbelianDual.InjectiveTarget O) := sorry

end SheafOfModules.RingedSite.AbelianDual.InjectiveTarget
