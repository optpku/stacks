module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Thickening

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe uX vX uY vY w

namespace RingedSite.ToposHom.Thickening

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [Y.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasSheafify Y.siteTopology AddCommGrpCat.{w}]
variable [Y.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The canonical kernel sequence of the structure map of a morphism of ringed topoi. -/
def kernelShortComplex (i : ToposHom X Y) :
    ShortComplex (SheafOfModules.{w} Y.structureSheaf) :=
  ShortComplex.mk (kernelIdeal_ι i) (kernelMap i) (kernelIdeal_ι_comp_kernelMap i)

/-- The kernel sequence of a thickening of ringed topoi is short exact. -/
theorem kernelShortComplex_shortExact (i : ToposHom X Y) [IsThickening i] :
    (kernelShortComplex i).ShortExact := sorry

end RingedSite.ToposHom.Thickening
