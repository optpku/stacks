module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Differentials
public import ReasLib.AlgebraicGeometry.RingedSite.CommRing.Pullback

/-!
# Relative differentials of a morphism of ringed sites

This file is the geometric bridge from the generic same-site relative-differentials owner to a
bundled morphism of commutative ringed-site presentations.  Its notation is scoped but globally
reusable.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open scoped RelativeDerivation

noncomputable section

universe u v

namespace RingedSite.Hom

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
variable [HasWeakSheafify JC AddCommGrpCat.{max u v}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O : Sheaf JC CommRingCat.{max u v}} {O' : Sheaf JD CommRingCat.{max u v}}

/-- The relative-differentials module of a morphism of commutative ringed
sites is formed from its adjoint inverse-image structure-sheaf map. -/
@[stacks 04BQ]
abbrev relativeDifferentials
    (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JC O)
      (RingedSite.ofCommRingSheaf JD O'))
    [h_adj : (f.base.sheafPushforwardContinuous CommRingCat.{max u v} JD JC).IsRightAdjoint] :
    ringedSiteModuleCategory JC O :=
  SheafOfModules.RingedSite.relativeDifferentials (inverseImageStructureSheafMap f)

/-- The universal relative derivation attached to a morphism of commutative ringed sites. -/
@[stacks 04BQ "universal derivation"]
abbrev relativeDifferential
    (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JC O)
      (RingedSite.ofCommRingSheaf JD O'))
    [h_adj : (f.base.sheafPushforwardContinuous CommRingCat.{max u v} JD JC).IsRightAdjoint] :
    Der[inverseImageStructureSheafMap f ; relativeDifferentials f] :=
  SheafOfModules.RingedSite.relativeDifferential (inverseImageStructureSheafMap f)

@[inherit_doc relativeDifferentials]
scoped[RingedSite.Hom] notation3:max "Ω[" f "]" => RingedSite.Hom.relativeDifferentials f

@[inherit_doc relativeDifferential]
scoped[RingedSite.Hom] notation3:max "d[" f "]" => RingedSite.Hom.relativeDifferential f

end RingedSite.Hom

-- Both data declarations are direct specializations of the generic universal construction.
