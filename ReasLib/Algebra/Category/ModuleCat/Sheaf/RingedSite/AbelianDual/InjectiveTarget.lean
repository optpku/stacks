/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.AbelianDual.Evaluation
public import ReasLib.CategoryTheory.Abelian.Injective.Coseparator
import Mathlib.Tactic.CrossRefAttribute

/-!
# Injective targets for abelian duality

An abelian duality target for a ringed site is relative to its structure sheaf: it must be
injective as an abelian sheaf and separate maps of module sheaves. This is weaker than being a
coseparator of the entire category of abelian sheaves.

The target universe only has to contain the site; it is independent of the universe of the
coefficient sheaf.
-/

@[expose] public section

open CategoryTheory

universe u v w z

namespace SheafOfModules.RingedSite.AbelianDual

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose
  (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasSheafify J AddCommGrpCat.{max u v z}]
variable (O : Sheaf J CommRingCat.{w})

/-- An injective abelian sheaf which separates maps of `O`-module sheaves. -/
@[stacks 01DQ "injective target for abelian duality"]
structure InjectiveTarget where
  /-- The abelian sheaf used as the target of the dual. -/
  obj : Sheaf J AddCommGrpCat.{max u v z}
  /-- The duality target is injective as an abelian sheaf. -/
  injective : Injective obj
  /-- Local maps into the duality target detect maps of `O`-module sheaves. -/
  separates : Separates O obj

attribute [instance] InjectiveTarget.injective

namespace InjectiveTarget

/-- An injective coseparator of abelian sheaves is, in particular, an injective target for
abelian duality over `O`. -/
@[stacks 01DQ "coseparator bridge"]
noncomputable def ofCoseparator
    (𝒥 : InjectiveCoseparator (Sheaf J AddCommGrpCat.{max u v z})) :
    InjectiveTarget O where
  obj := 𝒥.obj
  injective := 𝒥.injective
  separates := separates_of_isCoseparator O 𝒥.obj 𝒥.isCoseparator

end InjectiveTarget

end SheafOfModules.RingedSite.AbelianDual
