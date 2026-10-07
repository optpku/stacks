module

public import stacks_project.Chap91.Situation_91_9_1_Comparison

/-!
# Strict morphisms of thickenings of ringed topoi

A morphism of thickenings of ringed topoi is strict when the comparison
`(f')^* 𝒥 ⟶ ℐ` is an epimorphism of `𝒪'`-modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.ChangeOfRings

universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃ w

namespace RingedSite.ToposHom.Thickening

variable {A : RingedSite.{u₀, v₀, w}} {B : RingedSite.{u₁, v₁, w}}
variable {C : RingedSite.{u₂, v₂, w}} {D : RingedSite.{u₃, v₃, w}}
variable [A.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [B.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [C.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [D.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [A.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [B.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [C.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [D.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasSheafify B.siteTopology AddCommGrpCat.{w}]
variable [HasSheafify D.siteTopology AddCommGrpCat.{w}]
variable [B.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [D.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- A morphism of thickenings of ringed topoi is strict when the comparison
`(f')^* 𝒥 ⟶ ℐ` is an epimorphism of `𝒪'`-modules. -/
def IsStrict (sq : CommSquare A B C D)
    [IsThickening sq.upper] [IsThickening sq.lower]
    [(SheafOfModules.restrictScalars.{w} sq.right.structureMap).IsRightAdjoint] : Prop :=
  Epi (idealMap sq)

/-- Strictness is epimorphicity of the comparison `(f')^* 𝒥 ⟶ ℐ`. -/
theorem isStrict_iff (sq : CommSquare A B C D)
    [IsThickening sq.upper] [IsThickening sq.lower]
    [(SheafOfModules.restrictScalars.{w} sq.right.structureMap).IsRightAdjoint] :
    IsStrict sq ↔ Epi (idealMap sq) := sorry

/-- In the first-order case, strictness is equivalent to epimorphicity of the
comparison `f^* 𝒥 ⟶ ℐ` of `𝒪`-modules. -/
theorem isStrict_iff_sourceIdealMap (sq : CommSquare A B C D)
    [IsFirstOrderThickening sq.upper] [IsFirstOrderThickening sq.lower]
    [(SheafOfModules.restrictScalars.{w} sq.left.structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{w} sq.right.structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{w} sq.upper.structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{w} sq.lower.structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{w} (comp sq.left sq.lower).structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{w} (comp sq.upper sq.right).structureMap).IsRightAdjoint] :
    IsStrict sq ↔ Epi (sourceIdealMap sq) := sorry

end RingedSite.ToposHom.Thickening
