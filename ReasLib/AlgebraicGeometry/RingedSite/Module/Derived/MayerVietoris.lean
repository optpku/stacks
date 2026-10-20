/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.TopologyComparison
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Underlying
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.UnderlyingPushforwardComparison
public import ReasLib.CategoryTheory.Sites.TopologyComparison.MayerVietoris
import Mathlib.Tactic.CrossRefAttribute

/-!
# Mayer--Vietoris descent for derived module sheaves

The category-theoretic Mayer--Vietoris owner is additive-sheaf valued.  This leaf supplies the
module-valued condition by applying the exact derived forgetful functor, and specializes the
topology-comparison criteria to the canonical morphism of ringed sites.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology.Derived.Sections.MayerVietoris

noncomputable section

-- Generic bounded-below notation uses the standard model already chosen by `ModuleDerived`.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

universe u v w uι

namespace RingedSite.Hom.ModuleDerived.MayerVietoris

/-- The Mayer--Vietoris condition for a derived module object, expressed through its canonical
underlying derived additive sheaf. -/
@[stacks 0F18 "derived module Mayer--Vietoris condition",
  stacks 0F19 "derived module Mayer--Vietoris condition"]
noncomputable abbrev Condition
    (X : RingedSite.{u, v, w})
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasSheafify X.siteTopology AddCommGrpCat.{max u v}]
    (S : Square X) (K : RingedSite.Hom.ModuleDerived.{max u v} X) : Prop :=
  S.Condition X.siteTopology
    ((RingedSite.Hom.underlyingAbelianSheafDerived X).obj K)

namespace Condition

/-- The module condition is definitionally the additive Mayer--Vietoris condition after
forgetting scalars; this named bridge keeps downstream statements independent of the abbrev body. -/
theorem iff_underlying
    (X : RingedSite.{u, v, w})
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasSheafify X.siteTopology AddCommGrpCat.{max u v}]
    (S : Square X)
    (K : RingedSite.Hom.ModuleDerived.{max u v} X) :
    Condition X S K ↔
      S.Condition X.siteTopology
        ((RingedSite.Hom.underlyingAbelianSheafDerived X).obj K) := sorry

end Condition

end RingedSite.Hom.ModuleDerived.MayerVietoris

namespace RingedSite.TopologyComparison.ModuleDerived.MayerVietoris

variable {C : Type u} [Category.{v} C]
variable {τ τ' : GrothendieckTopology C}
variable [HasWeakSheafify τ RingCat.{w}]
variable [∀ F : Cᵒᵖ ⥤ RingCat.{w}, (𝟭 C).op.HasLeftKanExtension F]
variable [HasSheafify τ AddCommGrpCat.{max u v}]
variable [HasSheafify τ' AddCommGrpCat.{max u v}]
variable [τ.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [τ'.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

open RingedSite.Hom.ModuleDerived.MayerVietoris

/-- Lemma 21.29.3 (0F19): a sheafified-representable pushout square with monomorphic overlap
satisfies the canonical Mayer--Vietoris condition for every derived module object in the
essential image of the canonical topology-comparison pushforward. -/
@[stacks 0F19 "module Mayer--Vietoris descent across a topology comparison"]
theorem condition_of_essImage
    [HasWeakSheafify τ (Type (max u v))]
    (hle : τ' ≤ τ) (O' : Sheaf τ' RingCat.{w})
    [Functor.HasRightDerivedFunctor
      (RingedSite.Hom.modulePushforwardToDerived
        (RingedSite.TopologyComparison.hom hle O'))
      (RingedSite.Hom.ModuleQis (RingedSite.TopologyComparison.source hle O'))]
    (S : Square C)
    (hpushout :
      IsPushout
        (τ.sheafifiedRepresentableMap S.toY)
        (τ.sheafifiedRepresentableMap S.toZ)
        (τ.sheafifiedRepresentableMap S.inY)
        (τ.sheafifiedRepresentableMap S.inZ))
    (hmono : Mono (τ.sheafifiedRepresentableMap S.toY))
    (K' : RingedSite.Hom.ModuleDerived.{max u v}
      (RingedSite.TopologyComparison.target O'))
    (hK' : Functor.essImage
      (RingedSite.Hom.modulePushforwardDerived
        (RingedSite.TopologyComparison.hom hle O')) K') :
    Condition (RingedSite.TopologyComparison.target O') S K' := sorry

/-- Lemma 21.29.2 (0F18): if a family of squares detects the finer sheaf condition and the
module Mayer--Vietoris condition holds throughout the essential image of `Rε_*`, then for a
bounded-below derived module object that condition characterizes essential-image membership. -/
@[stacks 0F18 "bounded-below module essential-image criterion"]
theorem essImage_iff_condition
    {ι : Type uι}
    (hle : τ' ≤ τ) (O' : Sheaf τ' RingCat.{w})
    [Functor.HasRightDerivedFunctor
      (RingedSite.Hom.modulePushforwardToDerived
        (RingedSite.TopologyComparison.hom hle O'))
      (RingedSite.Hom.ModuleQis (RingedSite.TopologyComparison.source hle O'))]
    (S : ι → Square C)
    (hSheaf :
      ∀ ⦃F' : Cᵒᵖ ⥤ Type (max u v)⦄,
        Presheaf.IsSheaf τ' F' →
          (∀ i : ι,
            IsPullback
              (F'.map (S i).inY.op)
              (F'.map (S i).inZ.op)
              (F'.map (S i).toY.op)
              (F'.map (S i).toZ.op)) →
            Presheaf.IsSheaf τ F')
    (hcondition :
      ∀ ⦃L' : RingedSite.Hom.ModuleDerived.{max u v}
          (RingedSite.TopologyComparison.target O')⦄,
        Functor.essImage
            (RingedSite.Hom.modulePushforwardDerived
              (RingedSite.TopologyComparison.hom hle O')) L' →
          ∀ i : ι,
            Condition (RingedSite.TopologyComparison.target O') (S i) L')
    (K' : DerivedCategory.Plus
      (RingedSite.ModuleCat.{max u v}
        (RingedSite.TopologyComparison.target O'))) :
    Functor.essImage
        (RingedSite.Hom.modulePushforwardDerived
          (RingedSite.TopologyComparison.hom hle O'))
        (DerivedCategory.Plus.ι.obj K') ↔
      ∀ i : ι,
        Condition (RingedSite.TopologyComparison.target O') (S i)
          (DerivedCategory.Plus.ι.obj K') := sorry

end RingedSite.TopologyComparison.ModuleDerived.MayerVietoris

end
