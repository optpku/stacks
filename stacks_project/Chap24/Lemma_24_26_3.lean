module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Homotopy.QuasiIso
import StacksCheckRecall

/-!
# Lemma 24.26.3

Quasi-isomorphisms in the intrinsic DG homotopy category carry the canonical saturated
multiplicative-system and triangulation-compatibility instances.
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

/- Lemma 24.26.3 (1) (0FT4): DG homotopy quasi-isomorphisms form a saturated
multiplicative system. -/
@[stacks 0FT4]
#check
  (inferInstance : (Homotopy.quasiIso 𝒜).IsSaturatedMultiplicativeSystem)

/- Lemma 24.26.3 (2) (0FT4): this system is compatible with triangulation. -/
@[stacks 0FT4]
#check
  (inferInstance : (Homotopy.quasiIso 𝒜).IsCompatibleWithTriangulation)

end SheafOfModules.RingedSite.DifferentialGradedModule
