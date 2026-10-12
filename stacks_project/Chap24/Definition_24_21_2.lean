/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.DifferentialGraded
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open DifferentialGradedCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedModule

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable (𝒜 : DGA(𝒪))

/- Definition 24.21.2: the homotopy category `K(Mod(𝒜, d))` has the same objects as
`Mod(𝒜, d)` and closed degree-zero maps modulo degree-`-1` homotopy. Its canonical owner is
`DifferentialGradedCategory.K ℤ (Mod(𝒜, d))`. -/
@[stacks 0FS1] #check K ℤ (Mod(𝒜, d))

/- The canonical functor to the homotopy category passes a closed degree-zero map to its
homotopy class. -/
#check
  (Comp.inKFunctor :
    Comp ℤ (Mod(𝒜, d)) ⥤ K ℤ (Mod(𝒜, d)))

/- Every morphism in the homotopy category has a closed degree-zero representative. -/
#check
  (K.exists_rep :
    ∀ {L M : K ℤ (Mod(𝒜, d))} (f : L ⟶ M),
      ∃ g : CompHom L.obj M.obj, f = g.toHomotopyClass)

end

end SheafOfModules.RingedSite.DifferentialGradedModule
