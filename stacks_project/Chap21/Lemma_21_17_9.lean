/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.KFlat.Colimit
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section


variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/- Lemma 21.17.9: a sequential colimit of K-flat cochain complexes of modules on a ringed site is
K-flat. -/
@[stacks 06YR]
#check
  (CochainComplex.IsKFlat.sequentialColimit :
    ∀ F : ℕ ⥤ CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ,
      (∀ i, (F.obj i).IsKFlat) → (colimit F).IsKFlat)

end


end SheafOfModules.RingedSite
