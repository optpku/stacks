module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Thickening.Strict
import StacksCheckRecall

open CategoryTheory
open RingedSite.ToposHom

universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃ w

/- Definition 91.9.2: In Situation 91.9.1, a morphism of thickenings `(f, f')`
is strict when the comparison `(f')^* 𝒥 ⟶ ℐ` is a surjective map of
`𝒪'`-modules. -/
@[stacks 08M9] #check (RingedSite.ToposHom.Thickening.IsStrict :
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
    (sq : CommSquare A B C D)
    [IsThickening sq.upper] [IsThickening sq.lower]
    [(SheafOfModules.restrictScalars.{w} sq.right.structureMap).IsRightAdjoint], Prop)

/- Surjectivity of `(f')^* 𝒥 ⟶ ℐ` is epimorphicity of `idealMap`. -/
#check Thickening.isStrict_iff
