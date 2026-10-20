module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import ReasLib.CategoryTheory.Adjunction.LeftExact
public import ReasLib.CategoryTheory.Sites.Topos.Morphism
public import ReasLib.CategoryTheory.Sites.Topos.Embedding
public import ReasLib.CategoryTheory.Sites.MorphismOfSites
import Mathlib.Tactic.CrossRefAttribute

/-!
# Dense-subsite reductions of morphisms of topoi

This module packages a replacement of both sites presenting a morphism of
topoi by subcanonical finite-limit sites, together with representability data
for prescribed sheaf families.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u₁ u₂ u₃ uI uG v₁ v₂ v₃ w

namespace CategoryTheory

noncomputable section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable {I : Type uI} {G : Type uG}

namespace Functor.DenseSubsite

variable {C' : Type u₃} [Category.{v₃} C']

/-- Transport `Type w`-valued sheaves across a dense subsite, raising universes only as far as
the two sites require. -/
abbrev typeTransport
    (v : C ⥤ C') (J : GrothendieckTopology C) (J' : GrothendieckTopology C')
    [v.IsDenseSubsite J J'] :
    Sheaf J (Type w) ⥤ Sheaf J' (Type (max w u₁ u₃ v₁ v₃)) :=
  sheafCompose J uliftFunctor.{max w u₁ u₃ v₁ v₃, w} ⋙
    (IsDenseSubsite.sheafEquiv J J' v (Type (max w u₁ u₃ v₁ v₃))).functor

end Functor.DenseSubsite

namespace MorphismOfTopoiIn

/-- A site-level reduction of a morphism of topoi, together with prescribed source and target
families that become representable after the two dense-subsite transports. -/
structure Reduction
    (f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max w u₁ u₂ v₁ v₂} K J)
    (ℱ : I → Sheaf J (Type w)) (𝒢 : G → Sheaf K (Type w)) where
  /-- The replacement source carrier. -/
  sourceCarrier : Type (max w u₁ u₂ v₁ v₂)
  /-- The category structure on the replacement source. -/
  [sourceCategory : Category.{max w u₁ u₂ v₁ v₂} sourceCarrier]
  /-- The replacement source topology. -/
  sourceTopology : GrothendieckTopology sourceCarrier
  /-- The replacement source topology is subcanonical. -/
  [sourceSubcanonical : sourceTopology.Subcanonical]
  /-- The replacement source has finite limits. -/
  [sourceFiniteLimits : HasFiniteLimits sourceCarrier]
  /-- The dense comparison from the original source site. -/
  sourceFunctor : C ⥤ sourceCarrier
  /-- The source comparison is a dense subsite. -/
  [sourceDenseSubsite : sourceFunctor.IsDenseSubsite J sourceTopology]
  /-- The replacement target carrier. -/
  targetCarrier : Type (max w u₁ u₂ v₁ v₂)
  /-- The category structure on the replacement target. -/
  [targetCategory : Category.{max w u₁ u₂ v₁ v₂} targetCarrier]
  /-- The replacement target topology. -/
  targetTopology : GrothendieckTopology targetCarrier
  /-- The replacement target topology is subcanonical. -/
  [targetSubcanonical : targetTopology.Subcanonical]
  /-- The replacement target has finite limits. -/
  [targetFiniteLimits : HasFiniteLimits targetCarrier]
  /-- The dense comparison from the original target site. -/
  targetFunctor : D ⥤ targetCarrier
  /-- The target comparison is a dense subsite. -/
  [targetDenseSubsite : targetFunctor.IsDenseSubsite K targetTopology]
  /-- The site functor presenting the reduced lower morphism. -/
  siteFunctor : targetCarrier ⥤ sourceCarrier
  /-- The site functor is a morphism of sites. -/
  [siteFunctorIsMorphismOfSites : IsMorphismOfSites targetTopology sourceTopology siteFunctor]
  /-- The site functor preserves pullbacks. -/
  [siteFunctorPreservesPullbacks : PreservesLimitsOfShape WalkingCospan siteFunctor]
  /-- The site functor maps the chosen terminal object to a terminal object. -/
  siteFunctorMapsTerminal : IsTerminal (siteFunctor.obj (⊤_ targetCarrier))
  /-- The lower morphism of topoi in the replacement presentation. -/
  lowerMorphism : MorphismOfTopoiIn targetTopology sourceTopology
  /-- The inverse-image factorization square. -/
  factorizationSquare :
    Nonempty
      (CatCommSq
        (targetFunctor.sheafPushforwardContinuous
          (Type (max w u₁ u₂ v₁ v₂)) K targetTopology)
        lowerMorphism.inverseImageFunctor.obj
        f.inverseImageFunctor.obj
        (sourceFunctor.sheafPushforwardContinuous
          (Type (max w u₁ u₂ v₁ v₂)) J sourceTopology))
  /-- The specified source family becomes representable after transport. -/
  sourceFamilyRepresentable :
    ∀ i : I,
      (((Functor.DenseSubsite.typeTransport sourceFunctor J sourceTopology).obj
        (ℱ i)).obj).IsRepresentable
  /-- The specified target family becomes representable after transport. -/
  targetFamilyRepresentable :
    ∀ j : G,
      (((Functor.DenseSubsite.typeTransport targetFunctor K targetTopology).obj
        (𝒢 j)).obj).IsRepresentable

attribute [instance] Reduction.sourceCategory
attribute [instance] Reduction.sourceSubcanonical
attribute [instance] Reduction.sourceFiniteLimits
attribute [instance] Reduction.sourceDenseSubsite
attribute [instance] Reduction.targetCategory
attribute [instance] Reduction.targetSubcanonical
attribute [instance] Reduction.targetFiniteLimits
attribute [instance] Reduction.targetDenseSubsite
attribute [instance] Reduction.siteFunctorIsMorphismOfSites
attribute [instance] Reduction.siteFunctorPreservesPullbacks

namespace Reduction

/-- The site-morphism, finite-limit, terminal-object, factorization, and representability facts
stored by a reduction. -/
theorem spec
    {f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max w u₁ u₂ v₁ v₂} K J}
    {ℱ : I → Sheaf J (Type w)} {𝒢 : G → Sheaf K (Type w)}
    (R : Reduction f ℱ 𝒢) :
    IsMorphismOfSites R.targetTopology R.sourceTopology R.siteFunctor ∧
      PreservesLimitsOfShape WalkingCospan R.siteFunctor ∧
      Nonempty (IsTerminal (R.siteFunctor.obj (⊤_ R.targetCarrier))) ∧
      Nonempty
        (CatCommSq
          (R.targetFunctor.sheafPushforwardContinuous
            (Type (max w u₁ u₂ v₁ v₂)) K R.targetTopology)
          R.lowerMorphism.inverseImageFunctor.obj
          f.inverseImageFunctor.obj
          (R.sourceFunctor.sheafPushforwardContinuous
            (Type (max w u₁ u₂ v₁ v₂)) J R.sourceTopology)) ∧
      (∀ i : I,
        (((Functor.DenseSubsite.typeTransport R.sourceFunctor J R.sourceTopology).obj
          (ℱ i)).obj).IsRepresentable) ∧
      ∀ j : G,
        (((Functor.DenseSubsite.typeTransport R.targetFunctor K R.targetTopology).obj
          (𝒢 j)).obj).IsRepresentable := sorry

end Reduction

/-- Every morphism of topoi admits a finite-limit dense-subsite reduction in which chosen small
families on both sides become representable. -/
theorem exists_reduction
    [HasWeakSheafify J (Type (max u₁ v₁))]
    [HasWeakSheafify K (Type (max u₂ v₂))]
    [Small.{max w u₁ v₁} I] [Small.{max w u₂ v₂} G]
    (f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max w u₁ u₂ v₁ v₂} K J)
    (ℱ : I → Sheaf J (Type w)) (𝒢 : G → Sheaf K (Type w)) :
    Nonempty (Reduction f ℱ 𝒢) := sorry

end MorphismOfTopoiIn

end

end CategoryTheory
