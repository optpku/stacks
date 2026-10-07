module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Algebra.Resolution
import StacksCheckRecall

@[expose] public section

open CategoryTheory ComplexShape
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra

noncomputable section

universe u v uX vX

namespace SheafOfModules.RingedSite.DifferentialGradedAlgebra

section


variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (CategoryTheory.forget RingCat.{max u v})]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable (B : DGA(𝒪))

/- Lemma 24.31.2 (tag 0FU2): one quasi-isomorphic DG algebra works before pullback and after
every arbitrary `RingedSite.ToposHom` pullback between commutative ringed-topos presentations. -/
@[stacks 0FU2 "universal ringed-topos flat K-flat resolution"]
#check
  (exists_universallyTermwiseFlat_resolution B :
    ∃ (A : DGA(𝒪)) (f : A ⟶ B), QuasiIso f.hom ∧
      RingedSite.ToposHom.modulePullbackComplex.UniversallyTermwiseFlat.{uX, vX}
        A.toComplex)

end


end SheafOfModules.RingedSite.DifferentialGradedAlgebra
