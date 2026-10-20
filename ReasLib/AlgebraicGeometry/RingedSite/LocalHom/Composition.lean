module

public import ReasLib.AlgebraicGeometry.RingedSite.LocalHom
public import ReasLib.AlgebraicGeometry.RingedSite.CommRing.Pullback.Composition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition of local ringed-site morphisms

Locality is stable under composition across independently sized site categories. The instance is
registered on the bundled composite, so downstream developments reuse the objectwise result.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u₀ v₀ u₁ v₁ u₂ v₂ w

namespace RingedSite.Hom

variable {C₀ : Type u₀} [Category.{v₀} C₀]
variable {C₁ : Type u₁} [Category.{v₁} C₁]
variable {C₂ : Type u₂} [Category.{v₂} C₂]
variable {J₀ : GrothendieckTopology C₀}
variable {J₁ : GrothendieckTopology C₁}
variable {J₂ : GrothendieckTopology C₂}
variable [J₀.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J₁.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J₂.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {𝒪₀ : Sheaf J₀ CommRingCat.{w}}
variable {𝒪₁ : Sheaf J₁ CommRingCat.{w}}
variable {𝒪₂ : Sheaf J₂ CommRingCat.{w}}

namespace IsLocal

/-- Lemma 18.40.10 (04IG): a composite of local morphisms of commutative ringed-site
presentations is local. -/
@[stacks 04IG]
instance comp
    (f : RingedSite.Hom (RingedSite.ofCommRingSheaf J₀ 𝒪₀)
      (RingedSite.ofCommRingSheaf J₁ 𝒪₁))
    (g : RingedSite.Hom (RingedSite.ofCommRingSheaf J₁ 𝒪₁)
      (RingedSite.ofCommRingSheaf J₂ 𝒪₂))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} J₁ J₀).IsRightAdjoint]
    [(g.base.sheafPushforwardContinuous CommRingCat.{w} J₂ J₁).IsRightAdjoint]
    [f.IsLocal] [g.IsLocal] :
    IsLocal (h_adj := comp_pushforward_isRightAdjoint f g)
      (RingedSite.Hom.comp f g) := sorry

end IsLocal

end RingedSite.Hom
