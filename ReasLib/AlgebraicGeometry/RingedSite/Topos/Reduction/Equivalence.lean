/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Reduction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Common-site reductions of ringed-topos equivalences

A ringed-topos equivalence admits a reduction in which both presentations use one site and one
structure sheaf.  Keeping this specialization separate lets ordinary site-reduction consumers
avoid depending on its additional common-presentation API.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u v w uI uG

namespace RingedSite.ToposHom

open Functor.IsDenseSubsite

variable {X Y : RingedSite.{u, v, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable (f : ToposHom X Y)
variable [UnivLE.{max u v, w}]

/-- Lemma 18.7.2 (03CR), equivalence case: a reduction over one common site with one common
structure sheaf, so that the middle morphism is the identity. -/
@[stacks 03CR "common reduction"]
structure CommonReduction where
  /-- The common replacement category. -/
  carrier : Type u
  /-- The category structure on the common replacement. -/
  [category : Category.{v} carrier]
  /-- The common replacement topology. -/
  topology : GrothendieckTopology carrier
  /-- The common topology is subcanonical. -/
  [subcanonical : topology.Subcanonical]
  /-- The common replacement has all finite limits. -/
  [finiteLimits : HasFiniteLimits carrier]
  /-- The dense source comparison; its special cocontinuity is inferred canonically. -/
  sourceFunctor : X.carrier ⥤ carrier
  /-- The source comparison presents an equivalence. -/
  [sourceDenseSubsite : sourceFunctor.IsDenseSubsite X.siteTopology topology]
  /-- The dense target comparison; its special cocontinuity is inferred canonically. -/
  targetFunctor : Y.carrier ⥤ carrier
  /-- The target comparison presents an equivalence. -/
  [targetDenseSubsite : targetFunctor.IsDenseSubsite Y.siteTopology topology]
  /-- The common transported structure sheaf. -/
  structureSheaf : Sheaf topology RingCat.{w}
  /-- The common structure sheaf recovers the source structure sheaf. -/
  sourceTransport :
    (sourceFunctor.sheafPushforwardContinuous RingCat.{w}
      X.siteTopology topology).obj structureSheaf ≅ X.structureSheaf
  /-- The common structure sheaf recovers the target structure sheaf. -/
  targetTransport :
    (targetFunctor.sheafPushforwardContinuous RingCat.{w}
      Y.siteTopology topology).obj structureSheaf ≅ Y.structureSheaf
  /-- The inverse-image square whose middle edge is the identity of the common sheaf category. -/
  toposSquare :
    CatCommSq
      (targetFunctor.sheafPushforwardContinuous (Type w)
        Y.siteTopology topology)
      (Functor.id (Sheaf topology (Type w)))
      f.toTopos.inverseImage
      (sourceFunctor.sheafPushforwardContinuous (Type w)
        X.siteTopology topology)
  /-- Compatibility of the common-site factorization with the original structure map. -/
  structure_comm :
    f.toTopos.inverseImage.map
          (Functor.pushforwardUnderlyingIso targetFunctor targetTransport).hom ≫
        f.underlyingMap =
      (toposSquare.iso.app
          (Hom.underlyingStructureSheaf
            (RingedSite.ofRingSheaf topology structureSheaf))).hom ≫
        (Functor.pushforwardUnderlyingIso sourceFunctor sourceTransport).hom

attribute [instance] CommonReduction.category
attribute [instance] CommonReduction.subcanonical
attribute [instance] CommonReduction.finiteLimits
attribute [instance] CommonReduction.sourceDenseSubsite
attribute [instance] CommonReduction.targetDenseSubsite

/-- The common replacement ringed site. -/
noncomputable abbrev CommonReduction.site (R : CommonReduction f) : RingedSite.{u, v, w} :=
  RingedSite.ofRingSheaf R.topology R.structureSheaf

/-- The direct-image structure map for the source comparison, lifted uniquely through the
dense-subsite equivalence. -/
noncomputable def CommonReduction.sourceStructureMap (R : CommonReduction f) :
    R.structureSheaf ⟶
      (Functor.IsDenseSubsite.ringTransport R.sourceFunctor
        X.siteTopology R.topology).obj X.structureSheaf :=
  (sheafEquiv X.siteTopology R.topology R.sourceFunctor
      RingCat.{w}).inverse.preimage
    (R.sourceTransport.hom ≫
      (Functor.IsDenseSubsite.ringTransportIso R.sourceFunctor
        X.siteTopology R.topology X.structureSheaf).inv)

/-- The direct-image structure map for the target comparison, lifted uniquely through the
dense-subsite equivalence. -/
noncomputable def CommonReduction.targetStructureMap (R : CommonReduction f) :
    R.structureSheaf ⟶
      (Functor.IsDenseSubsite.ringTransport R.targetFunctor
        Y.siteTopology R.topology).obj Y.structureSheaf :=
  (sheafEquiv Y.siteTopology R.topology R.targetFunctor
      RingCat.{w}).inverse.preimage
    (R.targetTransport.hom ≫
      (Functor.IsDenseSubsite.ringTransportIso R.targetFunctor
        Y.siteTopology R.topology Y.structureSheaf).inv)

/-- The source common-site direct-image presentation preserves the canonical internal-ring
operations. -/
theorem CommonReduction.sourceComparison_isRingCompatible (R : CommonReduction f) :
    ToposHom.Direct.IsRingCompatible (X := X) (Y := R.site)
      (Functor.IsDenseSubsite.morphismOfTopoiIn R.sourceFunctor)
      (Functor.IsDenseSubsite.ringTransport R.sourceFunctor
        X.siteTopology R.topology)
      (Functor.IsDenseSubsite.ringTransportForgetIso R.sourceFunctor
        X.siteTopology R.topology)
      R.sourceStructureMap := sorry

/-- The source comparison into the common replacement ringed topos. -/
noncomputable def CommonReduction.sourceComparison (R : CommonReduction f) :
    ToposHom X R.site :=
  ToposHom.ofDirectImage
    (X := X) (Y := R.site)
    (Functor.IsDenseSubsite.morphismOfTopoiIn R.sourceFunctor)
    (Functor.IsDenseSubsite.ringTransport R.sourceFunctor
      X.siteTopology R.topology)
    (Functor.IsDenseSubsite.ringTransportForgetIso R.sourceFunctor
      X.siteTopology R.topology)
    R.sourceStructureMap
    (CommonReduction.sourceComparison_isRingCompatible (f := f) R)

/-- The target common-site direct-image presentation preserves the canonical internal-ring
operations. -/
theorem CommonReduction.targetComparison_isRingCompatible (R : CommonReduction f) :
    ToposHom.Direct.IsRingCompatible (X := Y) (Y := R.site)
      (Functor.IsDenseSubsite.morphismOfTopoiIn R.targetFunctor)
      (Functor.IsDenseSubsite.ringTransport R.targetFunctor
        Y.siteTopology R.topology)
      (Functor.IsDenseSubsite.ringTransportForgetIso R.targetFunctor
        Y.siteTopology R.topology)
      R.targetStructureMap := sorry

/-- The target comparison into the common replacement ringed topos. -/
noncomputable def CommonReduction.targetComparison (R : CommonReduction f) :
    ToposHom Y R.site :=
  ToposHom.ofDirectImage
    (X := Y) (Y := R.site)
    (Functor.IsDenseSubsite.morphismOfTopoiIn R.targetFunctor)
    (Functor.IsDenseSubsite.ringTransport R.targetFunctor
      Y.siteTopology R.topology)
    (Functor.IsDenseSubsite.ringTransportForgetIso R.targetFunctor
      Y.siteTopology R.topology)
    R.targetStructureMap
    (CommonReduction.targetComparison_isRingCompatible (f := f) R)

/-- The source comparison of a common reduction is a ringed equivalence. -/
instance CommonReduction.sourceComparison_isEquivalence (R : CommonReduction f) :
    R.sourceComparison.IsEquivalence := sorry

/-- The target comparison of a common reduction is a ringed equivalence. -/
instance CommonReduction.targetComparison_isEquivalence (R : CommonReduction f) :
    R.targetComparison.IsEquivalence := sorry

/-- The middle ringed-site morphism of a common reduction is the identity. -/
noncomputable abbrev CommonReduction.middle (R : CommonReduction f) : R.site ⟶ R.site :=
  RingedSite.Hom.id R.site

/-- The source type-sheaf equivalence of a common-site reduction. -/
noncomputable abbrev CommonReduction.sourceTypeEquiv (R : CommonReduction f) :
    Sheaf X.siteTopology (Type w) ≌ Sheaf R.topology (Type w) :=
  sheafEquiv X.siteTopology R.topology R.sourceFunctor (Type w)

/-- The target type-sheaf equivalence of a common-site reduction. -/
noncomputable abbrev CommonReduction.targetTypeEquiv (R : CommonReduction f) :
    Sheaf Y.siteTopology (Type w) ≌ Sheaf R.topology (Type w) :=
  sheafEquiv Y.siteTopology R.topology R.targetFunctor (Type w)

/-- Chosen families represented on the common replacement site. -/
@[stacks 03CR "equivalence, representation"]
structure CommonReduction.Represents {I : Type uI} {G : Type uG} (R : CommonReduction f)
    (Fs : I → Sheaf X.siteTopology (Type w))
    (Gs : G → Sheaf Y.siteTopology (Type w)) : Prop where
  /-- Every chosen source sheaf becomes representable. -/
  source : ∀ i : I, ((R.sourceTypeEquiv.functor.obj (Fs i)).obj).IsRepresentable
  /-- Every chosen target sheaf becomes representable. -/
  target : ∀ j : G, ((R.targetTypeEquiv.functor.obj (Gs j)).obj).IsRepresentable

/-- Lemma 18.7.2 (03CR), equivalence specialization: a ringed equivalence admits a common-site
reduction with identity middle morphism. -/
@[stacks 03CR "equivalence"]
theorem existsCommonReduction [f.IsEquivalence] : Nonempty (CommonReduction f) := sorry

/-- The equivalence specialization can retain clause (7) for prescribed representable families. -/
theorem existsCommonReductionRepresenting [f.IsEquivalence]
    {I : Type uI} {G : Type uG}
    (Fs : I → Sheaf X.siteTopology (Type w))
    (Gs : G → Sheaf Y.siteTopology (Type w)) :
    ∃ R : CommonReduction f, CommonReduction.Represents (f := f) R Fs Gs := sorry

-- The common-site carrier, structure sheaf, and comparisons are explicit fields or definitions;
-- any `sorryAx` is inherited from Prop-valued compatibility/equivalence obligations.

end RingedSite.ToposHom
