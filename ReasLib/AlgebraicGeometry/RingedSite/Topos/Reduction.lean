/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Subcanonical
public import ReasLib.Algebra.Category.Ring.KanExtension
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Forget
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom
public import ReasLib.CategoryTheory.Sites.DenseSubsite.Ring
public import ReasLib.CategoryTheory.Sites.DenseSubsite.Topos
public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose
public import ReasLib.CategoryTheory.Sites.SpecialCocontinuous
import Mathlib.Tactic.CrossRefAttribute

/-!
# Site reductions of morphisms of ringed topoi

An arbitrary morphism of ringed topoi can be replaced by a morphism induced by a finite-limit
functor between sites. The replacement datum is bundled so downstream arguments can use its
sites, transported structure sheaves, middle morphism, and compatibility square independently.
-/

@[expose] public section

open CategoryTheory Limits
open scoped MorphismOfTopoiIn

noncomputable section

universe u v w uI uG

namespace RingedSite.Hom

variable {X Y : RingedSite.{u, v, w}}
variable [UnivLE.{max u v, w}]

/-- The type-valued inverse image associated to a ringed-site morphism. -/
noncomputable abbrev typePullback (f : X ⟶ Y) :
    Sheaf Y.siteTopology (Type w) ⥤ Sheaf X.siteTopology (Type w) :=
  f.base.sheafPullback (Type w) Y.siteTopology X.siteTopology

/-- The inverse-image-form map on underlying structure sheaves associated to a ringed-site
morphism. Unlike `underlyingInverseImageMap`, this owner does not require first bundling the
site morphism as a morphism of topoi. -/
noncomputable abbrev underlyingPullbackMap (f : X ⟶ Y) :
    f.typePullback.obj (underlyingStructureSheaf Y) ⟶ underlyingStructureSheaf X :=
  ((f.base.sheafAdjunctionContinuous (Type w)
      Y.siteTopology X.siteTopology).homEquiv _ _).symm f.underlyingDirectImageMap

end RingedSite.Hom

namespace RingedSite.ToposHom

open Functor.IsDenseSubsite

variable {X Y : RingedSite.{u, v, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable (f : ToposHom X Y)
variable [UnivLE.{max u v, w}]

/-- Lemma 18.7.2 (03CR), clauses (1)--(6): a site reduction of an arbitrary morphism of
ringed topoi. The replacement sites and middle morphism are explicit fields, while the
replacement structure sheaves are their canonical dense-subsite transports. -/
@[stacks 03CR "site reduction"]
structure SiteReduction where
  /-- The replacement source category. -/
  sourceCarrier : Type u
  /-- The category structure on the replacement source. -/
  [sourceCategory : Category.{v} sourceCarrier]
  /-- The replacement source topology. -/
  sourceTopology : GrothendieckTopology sourceCarrier
  /-- The replacement source topology is subcanonical. -/
  [sourceSubcanonical : sourceTopology.Subcanonical]
  /-- The replacement source has all finite limits. -/
  [sourceFiniteLimits : HasFiniteLimits sourceCarrier]
  /-- The dense comparison from the original source presentation; its special cocontinuity is
  inferred canonically. -/
  sourceFunctor : X.carrier ⥤ sourceCarrier
  /-- The source comparison presents an equivalence of topoi. -/
  [sourceDenseSubsite : sourceFunctor.IsDenseSubsite X.siteTopology sourceTopology]
  /-- The replacement target category. -/
  targetCarrier : Type u
  /-- The category structure on the replacement target. -/
  [targetCategory : Category.{v} targetCarrier]
  /-- The replacement target topology. -/
  targetTopology : GrothendieckTopology targetCarrier
  /-- The replacement target topology is subcanonical. -/
  [targetSubcanonical : targetTopology.Subcanonical]
  /-- The replacement target has all finite limits. -/
  [targetFiniteLimits : HasFiniteLimits targetCarrier]
  /-- The dense comparison from the original target presentation; its special cocontinuity is
  inferred canonically. -/
  targetFunctor : Y.carrier ⥤ targetCarrier
  /-- The target comparison presents an equivalence of topoi. -/
  [targetDenseSubsite : targetFunctor.IsDenseSubsite Y.siteTopology targetTopology]
  /-- The middle morphism induced by a morphism of the replacement sites. Its structure sheaves
  are the canonical dense-subsite transports of the original structure sheaves. -/
  middle :
    RingedSite.Hom
      (RingedSite.ofRingSheaf sourceTopology
        ((Functor.IsDenseSubsite.ringTransport sourceFunctor
          X.siteTopology sourceTopology).obj X.structureSheaf))
      (RingedSite.ofRingSheaf targetTopology
        ((Functor.IsDenseSubsite.ringTransport targetFunctor
          Y.siteTopology targetTopology).obj Y.structureSheaf))
  /-- The base functor of the middle morphism preserves all finite limits. -/
  [middlePreservesFiniteLimits : PreservesFiniteLimits middle.base]
  /-- The inverse-image square presenting the factorization of the underlying morphism of topoi. -/
  toposSquare :
    CatCommSq
      (targetFunctor.sheafPushforwardContinuous (Type w)
        Y.siteTopology targetTopology)
      middle.typePullback
      f.toTopos.inverseImage
      (sourceFunctor.sheafPushforwardContinuous (Type w)
        X.siteTopology sourceTopology)
  /-- Compatibility of the factorization square with the inverse-image structure-sheaf maps. -/
  structure_comm :
    f.toTopos.inverseImage.map
          (Functor.pushforwardUnderlyingIso targetFunctor
            (Functor.IsDenseSubsite.ringTransportIso targetFunctor
              Y.siteTopology targetTopology Y.structureSheaf)).hom ≫
        f.underlyingMap =
      (toposSquare.iso.app
          (Hom.underlyingStructureSheaf
            (RingedSite.ofRingSheaf targetTopology
              ((Functor.IsDenseSubsite.ringTransport targetFunctor
                Y.siteTopology targetTopology).obj
                Y.structureSheaf)))).hom ≫
        (sourceFunctor.sheafPushforwardContinuous (Type w)
          X.siteTopology sourceTopology).map middle.underlyingPullbackMap ≫
        (Functor.pushforwardUnderlyingIso sourceFunctor
          (Functor.IsDenseSubsite.ringTransportIso sourceFunctor
            X.siteTopology sourceTopology X.structureSheaf)).hom

attribute [instance] SiteReduction.sourceCategory
attribute [instance] SiteReduction.sourceSubcanonical
attribute [instance] SiteReduction.sourceFiniteLimits
attribute [instance] SiteReduction.sourceDenseSubsite
attribute [instance] SiteReduction.targetCategory
attribute [instance] SiteReduction.targetSubcanonical
attribute [instance] SiteReduction.targetFiniteLimits
attribute [instance] SiteReduction.targetDenseSubsite
attribute [instance] SiteReduction.middlePreservesFiniteLimits

/-- The canonical transported source structure sheaf of a reduction. -/
noncomputable abbrev SiteReduction.sourceStructure (R : SiteReduction f) :
    Sheaf R.sourceTopology RingCat.{w} :=
  (Functor.IsDenseSubsite.ringTransport R.sourceFunctor
    X.siteTopology R.sourceTopology).obj X.structureSheaf

/-- The canonical transported target structure sheaf of a reduction. -/
noncomputable abbrev SiteReduction.targetStructure (R : SiteReduction f) :
    Sheaf R.targetTopology RingCat.{w} :=
  (Functor.IsDenseSubsite.ringTransport R.targetFunctor
    Y.siteTopology R.targetTopology).obj Y.structureSheaf

/-- Continuous pushforward of the transported source structure sheaf recovers the original
source structure sheaf. -/
noncomputable abbrev SiteReduction.sourceTransport (R : SiteReduction f) :
    (R.sourceFunctor.sheafPushforwardContinuous RingCat.{w}
      X.siteTopology R.sourceTopology).obj R.sourceStructure ≅ X.structureSheaf :=
  Functor.IsDenseSubsite.ringTransportIso R.sourceFunctor
    X.siteTopology R.sourceTopology X.structureSheaf

/-- Continuous pushforward of the transported target structure sheaf recovers the original
target structure sheaf. -/
noncomputable abbrev SiteReduction.targetTransport (R : SiteReduction f) :
    (R.targetFunctor.sheafPushforwardContinuous RingCat.{w}
      Y.siteTopology R.targetTopology).obj R.targetStructure ≅ Y.structureSheaf :=
  Functor.IsDenseSubsite.ringTransportIso R.targetFunctor
    Y.siteTopology R.targetTopology Y.structureSheaf

/-- The replacement source ringed site of a reduction. -/
noncomputable abbrev SiteReduction.sourceSite (R : SiteReduction f) : RingedSite.{u, v, w} :=
  RingedSite.ofRingSheaf R.sourceTopology R.sourceStructure

/-- The replacement target ringed site of a reduction. -/
noncomputable abbrev SiteReduction.targetSite (R : SiteReduction f) : RingedSite.{u, v, w} :=
  RingedSite.ofRingSheaf R.targetTopology R.targetStructure

/-- The source dense-subsite direct-image presentation preserves the canonical internal-ring
operations. -/
theorem SiteReduction.sourceComparison_isRingCompatible (R : SiteReduction f) :
    ToposHom.Direct.IsRingCompatible (X := X) (Y := R.sourceSite)
      (Functor.IsDenseSubsite.morphismOfTopoiIn R.sourceFunctor)
      (Functor.IsDenseSubsite.ringTransport R.sourceFunctor
        X.siteTopology R.sourceTopology)
      (Functor.IsDenseSubsite.ringTransportForgetIso R.sourceFunctor
        X.siteTopology R.sourceTopology)
      (𝟙 R.sourceStructure) := sorry

/-- The source vertical morphism of ringed topoi presented by a site reduction. -/
noncomputable def SiteReduction.sourceComparison (R : SiteReduction f) :
    ToposHom X R.sourceSite :=
  ToposHom.ofDirectImage
    (X := X) (Y := R.sourceSite)
    (Functor.IsDenseSubsite.morphismOfTopoiIn R.sourceFunctor)
    (Functor.IsDenseSubsite.ringTransport R.sourceFunctor
      X.siteTopology R.sourceTopology)
    (Functor.IsDenseSubsite.ringTransportForgetIso R.sourceFunctor
      X.siteTopology R.sourceTopology)
    (𝟙 R.sourceStructure)
    (SiteReduction.sourceComparison_isRingCompatible (f := f) R)

/-- The target dense-subsite direct-image presentation preserves the canonical internal-ring
operations. -/
theorem SiteReduction.targetComparison_isRingCompatible (R : SiteReduction f) :
    ToposHom.Direct.IsRingCompatible (X := Y) (Y := R.targetSite)
      (Functor.IsDenseSubsite.morphismOfTopoiIn R.targetFunctor)
      (Functor.IsDenseSubsite.ringTransport R.targetFunctor
        Y.siteTopology R.targetTopology)
      (Functor.IsDenseSubsite.ringTransportForgetIso R.targetFunctor
        Y.siteTopology R.targetTopology)
      (𝟙 R.targetStructure) := sorry

/-- The target vertical morphism of ringed topoi presented by a site reduction. -/
noncomputable def SiteReduction.targetComparison (R : SiteReduction f) :
    ToposHom Y R.targetSite :=
  ToposHom.ofDirectImage
    (X := Y) (Y := R.targetSite)
    (Functor.IsDenseSubsite.morphismOfTopoiIn R.targetFunctor)
    (Functor.IsDenseSubsite.ringTransport R.targetFunctor
      Y.siteTopology R.targetTopology)
    (Functor.IsDenseSubsite.ringTransportForgetIso R.targetFunctor
      Y.siteTopology R.targetTopology)
    (𝟙 R.targetStructure)
    (SiteReduction.targetComparison_isRingCompatible (f := f) R)

/-- The source comparison of a reduction is a ringed equivalence. -/
instance SiteReduction.sourceComparison_isEquivalence (R : SiteReduction f) :
    R.sourceComparison.IsEquivalence := sorry

/-- The target comparison of a reduction is a ringed equivalence. -/
instance SiteReduction.targetComparison_isEquivalence (R : SiteReduction f) :
    R.targetComparison.IsEquivalence := sorry

/-- The equivalence on type-valued sheaves presented by the source dense subsite of a reduction. -/
noncomputable abbrev SiteReduction.sourceTypeEquiv (R : SiteReduction f) :
    Sheaf X.siteTopology (Type w) ≌ Sheaf R.sourceTopology (Type w) :=
  sheafEquiv X.siteTopology R.sourceTopology R.sourceFunctor (Type w)

/-- The equivalence on type-valued sheaves presented by the target dense subsite of a reduction. -/
noncomputable abbrev SiteReduction.targetTypeEquiv (R : SiteReduction f) :
    Sheaf Y.siteTopology (Type w) ≌ Sheaf R.targetTopology (Type w) :=
  sheafEquiv Y.siteTopology R.targetTopology R.targetFunctor (Type w)

/-- Clause (7) for a site reduction: chosen source and target families become representable on
the replacement sites. -/
@[stacks 03CR "(7), representation"]
structure SiteReduction.Represents {I : Type uI} {G : Type uG} (R : SiteReduction f)
    (Fs : I → Sheaf X.siteTopology (Type w))
    (Gs : G → Sheaf Y.siteTopology (Type w)) : Prop where
  /-- Every chosen source sheaf becomes representable. -/
  source : ∀ i : I, ((R.sourceTypeEquiv.functor.obj (Fs i)).obj).IsRepresentable
  /-- Every chosen target sheaf becomes representable. -/
  target : ∀ j : G, ((R.targetTypeEquiv.functor.obj (Gs j)).obj).IsRepresentable

/-- Lemma 18.7.2 (03CR), clauses (1)--(6): every arbitrary morphism of ringed topoi admits a
site reduction. -/
@[stacks 03CR "(1)-(6)"]
theorem existsSiteReduction : Nonempty (SiteReduction f) := sorry

/-- Lemma 18.7.2 (03CR), clause (7): a site reduction can simultaneously make any two chosen
families of sheaves representable. -/
@[stacks 03CR "(7)"]
theorem existsSiteReductionRepresenting {I : Type uI} {G : Type uG}
    (Fs : I → Sheaf X.siteTopology (Type w))
    (Gs : G → Sheaf Y.siteTopology (Type w)) :
    ∃ R : SiteReduction f, SiteReduction.Represents (f := f) R Fs Gs := sorry

-- Reduction witnesses are structures supplied by the existence theorems, never whole-declaration
-- choices. The ring transport itself is audited without `sorryAx` in `DenseSubsite.Ring`.
-- Any `sorryAx` reported for projections below is inherited from the Prop-valued square and
-- structure-map compatibility fields (and their equality-coherence glue), not from hidden
-- replacement carriers, functors, sheaves, or morphisms.

end RingedSite.ToposHom
