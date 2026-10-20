module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Thickening.Comparison
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Thickening
import StacksCheckRecall

open CategoryTheory

universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃ w

namespace RingedSite.ToposHom.Thickening

/- Situation 91.9.1
(1): a morphism of thickenings of ringed topoi `(f, f')` is a commutative diagram of ringed
topoi whose horizontal arrows are thickenings. -/
@[stacks 08M7] #check (RingedSite.ToposHom.Thickening.homMk :
  ∀ {A : RingedSite.{u₀, v₀, w}} {B : RingedSite.{u₁, v₁, w}}
    {C : RingedSite.{u₂, v₂, w}} {D : RingedSite.{u₃, v₃, w}}
    [A.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [B.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [C.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [D.siteTopology.HasSheafCompose (forget RingCat.{w})]
    (i : RingedSite.ToposHom A B) (f : RingedSite.ToposHom A C)
    (f' : RingedSite.ToposHom B D) (t : RingedSite.ToposHom C D)
    [RingedSite.ToposHom.IsThickening i] [RingedSite.ToposHom.IsThickening t]
    (cell : RingedSite.ToposHom.TwoIso (RingedSite.ToposHom.comp i f')
      (RingedSite.ToposHom.comp f t)),
    RingedSite.ToposHom.CommSquare A B C D)

/- Situation 91.9.1
(2): set ℐ = Ker(i^♯) ⊂ 𝒪' and 𝒥 = Ker(t^♯) ⊂ 𝒪_{B'}.
Then `(f')^♯` induces the 𝒪'-module map `(f')^* 𝒥 ⟶ ℐ`. -/
@[stacks 08M7] #check (RingedSite.ToposHom.Thickening.idealMap :
  ∀ {A : RingedSite.{u₀, v₀, w}} {B : RingedSite.{u₁, v₁, w}}
    {C : RingedSite.{u₂, v₂, w}} {D : RingedSite.{u₃, v₃, w}}
    [A.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [B.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [C.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [D.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [A.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    [B.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    [C.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    [D.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    [HasSheafify B.siteTopology AddCommGrpCat.{w}]
    [HasSheafify D.siteTopology AddCommGrpCat.{w}]
    [B.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [D.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (sq : RingedSite.ToposHom.CommSquare A B C D)
    [RingedSite.ToposHom.IsThickening sq.upper]
    [RingedSite.ToposHom.IsThickening sq.lower]
    [(SheafOfModules.restrictScalars.{w} sq.right.structureMap).IsRightAdjoint],
    sq.right.modulePullback.obj (RingedSite.ToposHom.ker sq.lower) ⟶
      RingedSite.ToposHom.ker sq.upper)

/- Situation 91.9.1
(3): if i and t are first-order thickenings, then `(f')^* 𝒥 = f^* 𝒥` and the map above
becomes an 𝒪-module map `f^* 𝒥 ⟶ ℐ`. -/
@[stacks 08M7] #check (RingedSite.ToposHom.Thickening.sourceIdealMap :
  ∀ {A : RingedSite.{u₀, v₀, w}} {B : RingedSite.{u₁, v₁, w}}
    {C : RingedSite.{u₂, v₂, w}} {D : RingedSite.{u₃, v₃, w}}
    [A.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [B.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [C.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [D.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [A.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    [B.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    [C.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    [D.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    [HasSheafify B.siteTopology AddCommGrpCat.{w}]
    [HasSheafify D.siteTopology AddCommGrpCat.{w}]
    [B.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [D.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (sq : RingedSite.ToposHom.CommSquare A B C D)
    [RingedSite.ToposHom.IsFirstOrderThickening sq.upper]
    [RingedSite.ToposHom.IsFirstOrderThickening sq.lower]
    [(SheafOfModules.restrictScalars.{w} sq.left.structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{w} sq.right.structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{w} sq.upper.structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{w} sq.lower.structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{w}
      (RingedSite.ToposHom.comp sq.left sq.lower).structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{w}
      (RingedSite.ToposHom.comp sq.upper sq.right).structureMap).IsRightAdjoint],
    sq.left.modulePullback.obj (RingedSite.ToposHom.idealModule sq.lower) ⟶
      RingedSite.ToposHom.idealModule sq.upper)

end RingedSite.ToposHom.Thickening
