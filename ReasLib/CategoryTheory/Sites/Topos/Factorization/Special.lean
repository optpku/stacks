module

public import ReasLib.CategoryTheory.Adjunction.LeftExact
public import ReasLib.CategoryTheory.Sites.MorphismOfSites
public import ReasLib.CategoryTheory.Sites.Precoverage.Continuous
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable
public import ReasLib.CategoryTheory.Sites.SpecialCocontinuous
public import ReasLib.CategoryTheory.Sites.Topos.Embedding
public import ReasLib.CategoryTheory.Sites.Topos.Morphism
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Special-cocontinuous site factorizations

This module owns replacement-site factorizations of morphisms of topoi through
a subcanonical finite-limit site.  It is independent of a particular chapter
construction.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Functor.IsDenseSubsite

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

namespace MorphismOfTopoiIn.Factorization

/-- Lemma 7.29.6 (03A2): a replacement-site factorization of a morphism of
topoi through a subcanonical finite-limit site. -/
structure SpecialSite
    (f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max (max u₁ v₁) (max u₂ v₂)} K J) where
  /-- The carrier of the replacement site. -/
  carrier : Type (max (max u₁ v₁) (max u₂ v₂))
  /-- The category structure on the replacement carrier. -/
  [category : Category carrier]
  /-- The replacement Grothendieck topology. -/
  topology : GrothendieckTopology carrier
  /-- The replacement topology is subcanonical. -/
  [subcanonical : topology.Subcanonical]
  /-- The replacement site has finite limits. -/
  [finiteLimits : HasFiniteLimits carrier]
  /-- The comparison functor from the source site. -/
  source : C ⥤ carrier
  /-- The source comparison is special cocontinuous. -/
  [sourceSpecial : source.IsSpecialCocontinuous J topology]
  /-- Under source subcanonicity, the source comparison is fully faithful. -/
  sourceFullyFaithful_of_subcanonical : J.Subcanonical → source.FullyFaithful
  /-- The functor presenting the target-side inverse-image construction. -/
  target : D ⥤ carrier
  /-- The target functor is continuous for selected precoverages. -/
  targetContinuous : Functor.Precoverage.IsContinuous target K.toPrecoverage topology.toPrecoverage
  /-- The target functor preserves pullbacks. -/
  targetPreservesPullbacks : PreservesLimitsOfShape WalkingCospan target
  /-- The target functor maps terminal objects to terminal objects. -/
  targetMapsTerminal :
    ∀ X : D, Limits.IsTerminal X → Nonempty (Limits.IsTerminal (target.obj X))
  /-- With pullbacks on the original target site, the target functor is continuous. -/
  targetIsContinuous_of_hasPullbacks : Limits.HasPullbacks D → target.IsContinuous K topology
  /-- The lower morphism of topoi in the factorization. -/
  lower :
    MorphismOfTopoiIn.{u₂, max (max u₁ v₁) (max u₂ v₂), v₂,
      max (max u₁ v₁) (max u₂ v₂), max (max u₁ v₁) (max u₂ v₂)} K topology
  /-- The inverse-image factorization square. -/
  square :
    CatCommSq
      (𝟭 (Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))))
      lower.inverseImageFunctor.obj
      f.inverseImageFunctor.obj
      (source.sheafPushforwardContinuous
        (Type (max (max u₁ v₁) (max u₂ v₂))) J topology)

attribute [instance] SpecialSite.category
attribute [instance] SpecialSite.subcanonical
attribute [instance] SpecialSite.finiteLimits
attribute [instance] SpecialSite.sourceSpecial

namespace SpecialSite

/-- The source-facing conditions carried by a special-site factorization. -/
theorem spec
    {f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max (max u₁ v₁) (max u₂ v₂)} K J}
    (F : SpecialSite (J := J) (K := K) f) :
    F.source.IsSpecialCocontinuous J F.topology ∧
      Functor.Precoverage.IsContinuous F.target K.toPrecoverage F.topology.toPrecoverage ∧
      PreservesLimitsOfShape WalkingCospan F.target ∧
      (∀ X : D, Limits.IsTerminal X → Nonempty (Limits.IsTerminal (F.target.obj X))) ∧
      (Limits.HasPullbacks D → F.target.IsContinuous K F.topology) ∧
      Nonempty
        (CatCommSq
          (𝟭 (Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))))
          F.lower.inverseImageFunctor.obj
          f.inverseImageFunctor.obj
          (F.source.sheafPushforwardContinuous
            (Type (max (max u₁ v₁) (max u₂ v₂))) J F.topology)) := sorry

/-- Lemma 7.29.6 (03A2): a morphism of topoi admits a special-site
factorization in the representable universe. -/
@[stacks 03A2]
theorem exists_of_morphism
    [HasWeakSheafify K (Type (max (max u₁ v₁) (max u₂ v₂)))]
    [HasSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max (max u₁ v₁) (max u₂ v₂)} K J) :
    Nonempty (SpecialSite (J := J) (K := K) f) := sorry

/-- A selected cover of the target maps to a selected cover of a replacement
site when the displayed Yoneda comparison is available. -/
theorem target_cover_mem
    [HasWeakSheafify K (Type (max (max u₁ v₁) (max u₂ v₂)))]
    [HasSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max (max u₁ v₁) (max u₂ v₂)} K J)
    {C0 : Type (max (max u₁ v₁) (max u₂ v₂))}
    [Category.{max (max (max u₁ u₂) v₁) v₂} C0]
    {J0 : GrothendieckTopology C0}
    (a : C ⥤ C0) [a.IsDenseSubsite J J0]
    {C' : Type (max (max u₁ v₁) (max u₂ v₂))}
    [Category.{max (max (max u₁ u₂) v₁) v₂} C']
    {J' : GrothendieckTopology C'} [J'.Subcanonical]
    (v0 : C0 ⥤ C') [v0.IsDenseSubsite J0 J']
    (hcover :
      ∀ ⦃X : C'⦄ (R : Presieve X),
        R ∈ J'.toPrecoverage X ↔
          ∃ (ι : Type (max (max u₁ v₁) (max u₂ v₂))) (Y : ι → C') (π : ∀ i, Y i ⟶ X),
            R = Presieve.ofArrows Y π ∧
              Presheaf.IsLocallySurjective J'
                (Limits.Sigma.desc (fun i ↦ (J'.yoneda.map (π i)).hom)))
    (u : D ⥤ C')
    (ρ :
      u ⋙ J'.yoneda ≅
        (GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, v₂, u₂} K ⋙
            f.inverseImageFunctor.obj) ⋙
          (sheafEquiv J J0 a (Type (max (max u₁ v₁) (max u₂ v₂)))).functor ⋙
            (sheafEquiv J0 J' v0
              (Type (max (max u₁ v₁) (max u₂ v₂)))).functor)
    {V : D} (S : K.Cover V) :
    Presieve.ofArrows (fun I : S.Arrow ↦ u.obj I.Y) (fun I ↦ u.map I.f) ∈
      J'.toPrecoverage (u.obj V) := sorry

end SpecialSite

/-- Remark 7.29.8 (03CK): a common replacement site for an equivalence of
topoi, with special-cocontinuous presentations from both source sites. -/
structure CommonSite
    (f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max (max u₁ v₁) (max u₂ v₂)} K J) where
  /-- The carrier of the common replacement site. -/
  carrier : Type (max (max u₁ v₁) (max u₂ v₂))
  /-- The category structure on the common replacement carrier. -/
  [category : Category.{max (max (max u₁ u₂) v₁) v₂} carrier]
  /-- The common replacement topology. -/
  topology : GrothendieckTopology carrier
  /-- The common replacement topology is subcanonical. -/
  [subcanonical : topology.Subcanonical]
  /-- The common replacement site has finite limits. -/
  [finiteLimits : HasFiniteLimits carrier]
  /-- The special-cocontinuous comparison from the source site. -/
  source : C ⥤ carrier
  /-- The source comparison is special cocontinuous. -/
  [sourceSpecial : source.IsSpecialCocontinuous J topology]
  /-- The special-cocontinuous comparison from the target site. -/
  target : D ⥤ carrier
  /-- The target comparison is special cocontinuous. -/
  [targetSpecial : target.IsSpecialCocontinuous K topology]
  /-- The inverse-image factorization square through the common site. -/
  square :
    CatCommSq
      (target.sheafPushforwardContinuous
        (Type (max (max u₁ v₁) (max u₂ v₂))) K topology)
      (MorphismOfTopoiIn.id topology).inverseImageFunctor.obj
      f.inverseImageFunctor.obj
      (source.sheafPushforwardContinuous
        (Type (max (max u₁ v₁) (max u₂ v₂))) J topology)

attribute [instance] CommonSite.category
attribute [instance] CommonSite.subcanonical
attribute [instance] CommonSite.finiteLimits
attribute [instance] CommonSite.sourceSpecial
attribute [instance] CommonSite.targetSpecial

namespace CommonSite

/-- The source-level conditions carried by a common-site factorization. -/
theorem spec
    {f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max (max u₁ v₁) (max u₂ v₂)} K J}
    (F : CommonSite (J := J) (K := K) f) :
    F.source.IsSpecialCocontinuous J F.topology ∧
      F.target.IsSpecialCocontinuous K F.topology ∧
      Nonempty
        (CatCommSq
          (F.target.sheafPushforwardContinuous
            (Type (max (max u₁ v₁) (max u₂ v₂))) K F.topology)
          (MorphismOfTopoiIn.id F.topology).inverseImageFunctor.obj
          f.inverseImageFunctor.obj
          (F.source.sheafPushforwardContinuous
            (Type (max (max u₁ v₁) (max u₂ v₂))) J F.topology)) := sorry

/-- Remark 7.29.8 (03CK): an equivalence of topoi admits a common special-site
factorization. -/
@[stacks 03CK]
theorem exists_of_equivalence
    [HasWeakSheafify K (Type (max (max u₁ v₁) (max u₂ v₂)))]
    [HasSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max (max u₁ v₁) (max u₂ v₂)} K J)
    [f.inverseImageFunctor.obj.IsEquivalence] :
    Nonempty (CommonSite (J := J) (K := K) f) := sorry

section Comparison

variable {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'}
  (f : MorphismOfTopoiIn K J)
  (source : C ⥤ C') [source.IsSpecialCocontinuous J J']
  [∀ P : Cᵒᵖ ⥤ Type w, source.op.HasPointwiseRightKanExtension P]
  (target : D ⥤ C') [target.IsSpecialCocontinuous K J']
  [∀ P : Dᵒᵖ ⥤ Type w, target.op.HasPointwiseRightKanExtension P]
  (sq :
    CatCommSq
      (target.sheafPushforwardContinuous (Type w) K J')
      (MorphismOfTopoiIn.id J').inverseImageFunctor.obj
      f.inverseImageFunctor.obj
      (source.sheafPushforwardContinuous (Type w) J J'))

/-- The base-change (mate) transformation of a common-site inverse-image square with respect to
the continuous/cocontinuous pushforward adjunctions of `target` and `source`. -/
noncomputable def cocontinuousComparison :
    target.sheafPushforwardCocontinuous (Type w) K J' ⟶
      f.inverseImageFunctor.obj ⋙ source.sheafPushforwardCocontinuous (Type w) J J' :=
  (mateEquiv (target.sheafAdjunctionCocontinuous (Type w) K J')
    (source.sheafAdjunctionCocontinuous (Type w) J J')
    (CatCommSq.iso (self := sq) _ _ _ _).inv).natTrans

/-- Remark 7.29.8 (03CK): a common-site inverse-image square identifies the two cocontinuous
direct images. Both cocontinuous direct images are equivalences (Lemma 7.29.1, 03A0), so the unit
and counit of the two pushforward adjunctions are invertible; the comparison is obtained by
conjugating the square with them. Its inverse is `cocontinuousComparison`. -/
noncomputable def cocontinuousComparisonIso :
    f.inverseImageFunctor.obj ⋙ source.sheafPushforwardCocontinuous (Type w) J J' ≅
      target.sheafPushforwardCocontinuous (Type w) K J' :=
  haveI : (target.sheafPushforwardCocontinuous (Type w) K J').IsEquivalence :=
    Functor.IsSpecialCocontinuous.directImage_isEquivalence target
  haveI : (source.sheafPushforwardCocontinuous (Type w) J J').IsEquivalence :=
    Functor.IsSpecialCocontinuous.directImage_isEquivalence source
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight
      (asIso (target.sheafAdjunctionCocontinuous (Type w) K J').counit).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (CatCommSq.iso (self := sq) _ _ _ _) _ ≪≫
      Functor.isoWhiskerRight (Functor.leftUnitor _) _ ≪≫
      (asIso (source.sheafAdjunctionCocontinuous (Type w) J J').unit).symm) ≪≫
    Functor.rightUnitor _

/-- The inverse of the common-site comparison is the base-change transformation of the square. -/
theorem cocontinuousComparisonIso_inv :
    (cocontinuousComparisonIso f source target sq).inv =
      cocontinuousComparison f source target sq := sorry

end Comparison

end CommonSite

end MorphismOfTopoiIn.Factorization

namespace Functor.IsDenseSubsite

/-- Dense subsite presentations compose on the right with a dense subsite
after an equivalence on the source side. -/
theorem comp_of_equivalence_left
    {C0 : Type*} [Category* C0]
    {C' : Type*} [Category* C']
    {J0 : GrothendieckTopology C0} {J' : GrothendieckTopology C'}
    (a : C ⥤ C0) (v0 : C0 ⥤ C')
    [a.IsDenseSubsite J J0] [a.IsEquivalence]
    [v0.IsDenseSubsite J0 J'] :
    (a ⋙ v0).IsDenseSubsite J J' := sorry

end Functor.IsDenseSubsite

end CategoryTheory
