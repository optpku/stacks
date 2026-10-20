/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.CommRing.Pullback
public import ReasLib.CategoryTheory.Sites.Topos.Composition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition of inverse-image structure-sheaf maps

This leaf records the coherent comparison between the inverse-image-form
structure-sheaf maps of two composable morphisms of commutative ringed-site
presentations on independently sized site categories. The concrete nested-pullback composite is
kept separate from the canonical transport to the pullback along the composite base functor.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u₀ v₀ u₁ v₁ u₂ v₂ w

namespace RingedSite.Hom

section Base

variable {C₀ : Type u₀} [Category.{v₀} C₀]
variable {C₁ : Type u₁} [Category.{v₁} C₁]
variable {C₂ : Type u₂} [Category.{v₂} C₂]
variable {J₀ : GrothendieckTopology C₀}
variable {J₁ : GrothendieckTopology C₁}
variable {J₂ : GrothendieckTopology C₂}
variable [J₀.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J₁.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J₂.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {𝒜₀ : Sheaf J₀ CommRingCat.{w}}
variable {𝒜₁ : Sheaf J₁ CommRingCat.{w}}
variable {𝒜₂ : Sheaf J₂ CommRingCat.{w}}

/-- The displayed composite base functor of composable commutative ringed-site presentations is
continuous, independently of the coefficient universe. -/
instance commRingBaseCompIsContinuous
    (p : RingedSite.Hom (RingedSite.ofCommRingSheaf J₀ 𝒜₀)
      (RingedSite.ofCommRingSheaf J₁ 𝒜₁))
    (q : RingedSite.Hom (RingedSite.ofCommRingSheaf J₁ 𝒜₁)
      (RingedSite.ofCommRingSheaf J₂ 𝒜₂)) :
    Functor.IsContinuous (q.base ⋙ p.base) J₂ J₀ :=
  (RingedSite.Hom.comp p q).isMorphismOfSites.toIsContinuous

/-- The continuous commutative-ring sheaf pushforward of a composite has its canonical right
adjoint whenever the two component pushforwards do. -/
@[stacks 03D6 "right adjoint for a composite sheaf pushforward"]
instance comp_pushforward_isRightAdjoint
    (p : RingedSite.Hom (RingedSite.ofCommRingSheaf J₀ 𝒜₀)
      (RingedSite.ofCommRingSheaf J₁ 𝒜₁))
    (q : RingedSite.Hom (RingedSite.ofCommRingSheaf J₁ 𝒜₁)
      (RingedSite.ofCommRingSheaf J₂ 𝒜₂))
    [(p.base.sheafPushforwardContinuous CommRingCat.{w} J₁ J₀).IsRightAdjoint]
    [(q.base.sheafPushforwardContinuous CommRingCat.{w} J₂ J₁).IsRightAdjoint] :
    ((q.base ⋙ p.base).sheafPushforwardContinuous
      CommRingCat.{w} J₂ J₀).IsRightAdjoint := sorry

end Base

section CommRing

variable {C₀ : Type u₀} [Category.{v₀} C₀]
variable {C₁ : Type u₁} [Category.{v₁} C₁]
variable {C₂ : Type u₂} [Category.{v₂} C₂]
variable {J₀ : GrothendieckTopology C₀}
variable {J₁ : GrothendieckTopology C₁}
variable {J₂ : GrothendieckTopology C₂}
variable [J₀.HasSheafCompose
  (forget₂ CommRingCat.{max u₀ v₀ u₁ v₁ u₂ v₂} RingCat.{max u₀ v₀ u₁ v₁ u₂ v₂})]
variable [J₁.HasSheafCompose
  (forget₂ CommRingCat.{max u₀ v₀ u₁ v₁ u₂ v₂} RingCat.{max u₀ v₀ u₁ v₁ u₂ v₂})]
variable [J₂.HasSheafCompose
  (forget₂ CommRingCat.{max u₀ v₀ u₁ v₁ u₂ v₂} RingCat.{max u₀ v₀ u₁ v₁ u₂ v₂})]
variable [HasWeakSheafify J₀ CommRingCat.{max u₀ v₀ u₁ v₁ u₂ v₂}]
variable [HasWeakSheafify J₁ CommRingCat.{max u₀ v₀ u₁ v₁ u₂ v₂}]
variable {𝒪₀ : Sheaf J₀ CommRingCat.{max u₀ v₀ u₁ v₁ u₂ v₂}}
variable {𝒪₁ : Sheaf J₁ CommRingCat.{max u₀ v₀ u₁ v₁ u₂ v₂}}
variable {𝒪₂ : Sheaf J₂ CommRingCat.{max u₀ v₀ u₁ v₁ u₂ v₂}}

/-- Pulling back the inverse-image structure-sheaf map of `q` along `p` gives the first
map in the inverse-image structure-sheaf map of `p ≫ q`. -/
@[stacks 03D6 "pullback of the inverse-image structure-sheaf map"]
noncomputable abbrev pullbackInverseImageStructureSheafMap
    (p : RingedSite.Hom (RingedSite.ofCommRingSheaf J₀ 𝒪₀)
      (RingedSite.ofCommRingSheaf J₁ 𝒪₁))
    (q : RingedSite.Hom (RingedSite.ofCommRingSheaf J₁ 𝒪₁)
      (RingedSite.ofCommRingSheaf J₂ 𝒪₂))
    [p_adj : (p.base.sheafPushforwardContinuous
      CommRingCat.{max u₀ v₀ u₁ v₁ u₂ v₂} J₁ J₀).IsRightAdjoint]
    [q_adj : (q.base.sheafPushforwardContinuous
      CommRingCat.{max u₀ v₀ u₁ v₁ u₂ v₂} J₂ J₁).IsRightAdjoint] :
    (p.base.sheafPullback CommRingCat.{max u₀ v₀ u₁ v₁ u₂ v₂} J₁ J₀).obj
        ((q.base.sheafPullback CommRingCat.{max u₀ v₀ u₁ v₁ u₂ v₂} J₂ J₁).obj 𝒪₂) ⟶
      (p.base.sheafPullback CommRingCat.{max u₀ v₀ u₁ v₁ u₂ v₂} J₁ J₀).obj 𝒪₁ :=
  (@Functor.leftAdjoint _ _ _ _
    (p.base.sheafPushforwardContinuous
      CommRingCat.{max u₀ v₀ u₁ v₁ u₂ v₂} J₁ J₀) p_adj).map
      (inverseImageStructureSheafMap (h_adj := q_adj) q)

/-- The inverse-image structure-sheaf composite on the nested pullback source.

For `p : X₀ ⟶ X₁` and `q : X₁ ⟶ X₂`, this is
`p⁻¹(q⁻¹𝒪₂) ⟶ p⁻¹𝒪₁ ⟶ 𝒪₀` before transporting the source along the canonical
comparison with `(p ≫ q)⁻¹𝒪₂`. -/
@[stacks 03D6 "inverse-image structure-sheaf composition"]
noncomputable abbrev inverseImageStructureSheafMapComposite
    (p : RingedSite.Hom (RingedSite.ofCommRingSheaf J₀ 𝒪₀)
      (RingedSite.ofCommRingSheaf J₁ 𝒪₁))
    (q : RingedSite.Hom (RingedSite.ofCommRingSheaf J₁ 𝒪₁)
      (RingedSite.ofCommRingSheaf J₂ 𝒪₂))
    [p_adj : (p.base.sheafPushforwardContinuous
      CommRingCat.{max u₀ v₀ u₁ v₁ u₂ v₂} J₁ J₀).IsRightAdjoint]
    [q_adj : (q.base.sheafPushforwardContinuous
      CommRingCat.{max u₀ v₀ u₁ v₁ u₂ v₂} J₂ J₁).IsRightAdjoint] :
    (p.base.sheafPullback CommRingCat.{max u₀ v₀ u₁ v₁ u₂ v₂} J₁ J₀).obj
        ((q.base.sheafPullback CommRingCat.{max u₀ v₀ u₁ v₁ u₂ v₂} J₂ J₁).obj 𝒪₂) ⟶ 𝒪₀ :=
  pullbackInverseImageStructureSheafMap (p_adj := p_adj) (q_adj := q_adj) p q ≫
    inverseImageStructureSheafMap (h_adj := p_adj) p

/-- After the canonical pullback-composition transport, the nested inverse-image structure-sheaf
map is the inverse-image structure-sheaf map of the composite ringed-site morphism. -/
@[stacks 03D6 "inverse-image structure-sheaf composition compatibility"]
theorem inverseImageStructureSheafMap_comp_common
    (p : RingedSite.Hom (RingedSite.ofCommRingSheaf J₀ 𝒪₀)
      (RingedSite.ofCommRingSheaf J₁ 𝒪₁))
    (q : RingedSite.Hom (RingedSite.ofCommRingSheaf J₁ 𝒪₁)
      (RingedSite.ofCommRingSheaf J₂ 𝒪₂))
    [(p.base.sheafPushforwardContinuous
      CommRingCat.{max u₀ v₀ u₁ v₁ u₂ v₂} J₁ J₀).IsRightAdjoint]
    [(q.base.sheafPushforwardContinuous
      CommRingCat.{max u₀ v₀ u₁ v₁ u₂ v₂} J₂ J₁).IsRightAdjoint] :
    ((CategoryTheory.Functor.sheafPullbackComp'
        (A := CommRingCat.{max u₀ v₀ u₁ v₁ u₂ v₂}) (J := J₂) (K := J₁)
        (L := J₀) (u := q.base) (v := p.base) (euv := Iso.refl _)).inv.app 𝒪₂) ≫
      inverseImageStructureSheafMapComposite p q =
    inverseImageStructureSheafMap
      (h_adj := comp_pushforward_isRightAdjoint p q) (RingedSite.Hom.comp p q) := sorry

/-- The nested inverse-image structure-sheaf composite is characterized on the adjunction side
by the composite pushforward-form structure-sheaf map. -/
theorem inverseImageStructureSheafMapComposite_homEquiv
    (p : RingedSite.Hom (RingedSite.ofCommRingSheaf J₀ 𝒪₀)
      (RingedSite.ofCommRingSheaf J₁ 𝒪₁))
    (q : RingedSite.Hom (RingedSite.ofCommRingSheaf J₁ 𝒪₁)
      (RingedSite.ofCommRingSheaf J₂ 𝒪₂))
    [(p.base.sheafPushforwardContinuous
      CommRingCat.{max u₀ v₀ u₁ v₁ u₂ v₂} J₁ J₀).IsRightAdjoint]
    [(q.base.sheafPushforwardContinuous
      CommRingCat.{max u₀ v₀ u₁ v₁ u₂ v₂} J₂ J₁).IsRightAdjoint] :
    (((q.base ⋙ p.base).sheafAdjunctionContinuous
      CommRingCat.{max u₀ v₀ u₁ v₁ u₂ v₂} J₂ J₀).homEquiv _ _)
      (((CategoryTheory.Functor.sheafPullbackComp'
          (A := CommRingCat.{max u₀ v₀ u₁ v₁ u₂ v₂}) (J := J₂) (K := J₁)
          (L := J₀) (u := q.base) (v := p.base) (euv := Iso.refl _)).inv.app 𝒪₂) ≫
        inverseImageStructureSheafMapComposite p q) =
      Functor.preimage (sheafCompose J₂
        (forget₂ CommRingCat.{max u₀ v₀ u₁ v₁ u₂ v₂} RingCat.{max u₀ v₀ u₁ v₁ u₂ v₂}))
        (q.structureSheafMap ≫
          (q.base.sheafPushforwardContinuous
            RingCat.{max u₀ v₀ u₁ v₁ u₂ v₂} J₂ J₁).map p.structureSheafMap :
          (sheafCompose J₂
            (forget₂ CommRingCat.{max u₀ v₀ u₁ v₁ u₂ v₂}
              RingCat.{max u₀ v₀ u₁ v₁ u₂ v₂})).obj 𝒪₂ ⟶
            (sheafCompose J₂
              (forget₂ CommRingCat.{max u₀ v₀ u₁ v₁ u₂ v₂}
                RingCat.{max u₀ v₀ u₁ v₁ u₂ v₂})).obj
              ((q.base.sheafPushforwardContinuous
                CommRingCat.{max u₀ v₀ u₁ v₁ u₂ v₂} J₂ J₁).obj
                ((p.base.sheafPushforwardContinuous
                  CommRingCat.{max u₀ v₀ u₁ v₁ u₂ v₂} J₁ J₀).obj 𝒪₀))) := sorry

end CommRing

end RingedSite.Hom
