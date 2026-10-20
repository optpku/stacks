module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Bimodule
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule
open scoped SheafOfModules.RingedSite.DifferentialGradedBimodule

noncomputable section

universe u v

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable {𝒜 𝒝 : DGA(𝒪)} (M N : Mod(𝒜, 𝒝, d))

/- Definition 24.17.1 (1): a differential graded `(𝒜, 𝒝)`-bimodule on a ringed site `(C, 𝒪)`
is a complex of `𝒪`-modules with `𝒪`-bilinear left `𝒜`-action and right `𝒝`-action,
associative on each side, mutually commuting, unital for `1` in `𝒜⁰` and `1` in `𝒝⁰`,
and satisfying the graded Leibniz rules. -/
@[stacks 0FRQ] #check
  (SheafOfModules.RingedSite.DifferentialGradedBimodule 𝒜 𝒝 : Type (max (u + 1) (v + 1)))

/- The right multiplication is the packaged right differential graded `𝒝`-module. -/
#check (M.toRightModule : Mod(𝒝, d))

/- The left multiplication is the extra left differential graded `𝒜`-action. -/
#check M.leftMul

/- The inherited right multiplication of the underlying right module. -/
#check M.toRightModule.smul

/- Definition 24.17.1 (2): a homomorphism of differential graded `(𝒜, 𝒝)`-bimodules is a map
of complexes of `𝒪`-modules compatible with both multiplication maps. -/
@[stacks 0FRQ] #check
  (SheafOfModules.RingedSite.DifferentialGradedBimodule.Hom M N : Type (max u v))

/- Morphisms in the bimodule category are the same homomorphisms. -/
#check (M ⟶ N)

end
