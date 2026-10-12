/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Reduction.Equivalence
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 18.7.2

Source-facing checks for reduction of arbitrary morphisms of ringed topoi to morphisms presented
by finite-limit functors of sites.
-/

open CategoryTheory Limits

universe u v w uI uG

namespace RingedSite.ToposHom

variable {X Y : RingedSite.{u, v, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
  [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable (f : ToposHom X Y)
variable [UnivLE.{max u v, w}]

/- Lemma 18.7.2 (03CR), clauses (1)--(6): an arbitrary morphism of ringed topoi admits a bundled
site reduction with canonical transported structure sheaves. -/
@[stacks 03CR "(1)-(6)"]
#check (existsSiteReduction f : Nonempty (SiteReduction f))

variable (R : SiteReduction f)

/- Lemma 18.7.2 (03CR) (1): the source comparison is induced by a special cocontinuous functor
and is a ringed equivalence. -/
#check (Functor.IsDenseSubsite.isSpecialCocontinuous R.sourceFunctor :
  R.sourceFunctor.IsSpecialCocontinuous X.siteTopology R.sourceTopology)
#check (R.sourceComparison : ToposHom X R.sourceSite)
#check (SiteReduction.sourceComparison_isEquivalence f R : R.sourceComparison.IsEquivalence)

/- Lemma 18.7.2 (03CR) (2): the target comparison is induced by a special cocontinuous functor
and is a ringed equivalence. -/
#check (Functor.IsDenseSubsite.isSpecialCocontinuous R.targetFunctor :
  R.targetFunctor.IsSpecialCocontinuous Y.siteTopology R.targetTopology)
#check (R.targetComparison : ToposHom Y R.targetSite)
#check (SiteReduction.targetComparison_isEquivalence f R : R.targetComparison.IsEquivalence)

/- Lemma 18.7.2 (03CR) (3): the replacement source structure sheaf is the canonical direct-image
transport, with its canonical comparison to the original structure sheaf. -/
#check (R.sourceStructure : Sheaf R.sourceTopology RingCat.{w})
#check (R.sourceTransport :
  (R.sourceFunctor.sheafPushforwardContinuous RingCat.{w}
    X.siteTopology R.sourceTopology).obj R.sourceStructure ≅ X.structureSheaf)

/- Lemma 18.7.2 (03CR) (4): the replacement target structure sheaf is the canonical direct-image
transport, with its canonical comparison to the original structure sheaf. -/
#check (R.targetStructure : Sheaf R.targetTopology RingCat.{w})
#check (R.targetTransport :
  (R.targetFunctor.sheafPushforwardContinuous RingCat.{w}
    Y.siteTopology R.targetTopology).obj R.targetStructure ≅ Y.structureSheaf)

/- Lemma 18.7.2 (03CR) (5): both replacement sites are subcanonical and have all finite limits. -/
#check (R.sourceSubcanonical : R.sourceTopology.Subcanonical)
#check (R.sourceFiniteLimits : HasFiniteLimits R.sourceCarrier)
#check (R.targetSubcanonical : R.targetTopology.Subcanonical)
#check (R.targetFiniteLimits : HasFiniteLimits R.targetCarrier)

/- Lemma 18.7.2 (03CR) (6): the middle morphism is induced by a continuous finite-limit functor,
and the bundled squares record compatibility with the original ringed-topos morphism. -/
#check (R.middle : R.sourceSite ⟶ R.targetSite)
#check (RingedSite.Hom.base_isContinuous R.middle :
  R.middle.base.IsContinuous R.targetTopology R.sourceTopology)
#check (R.middlePreservesFiniteLimits : PreservesFiniteLimits R.middle.base)
#check R.toposSquare
#check R.structure_comm

variable {I : Type uI} {G : Type uG}
variable (Fs : I → Sheaf X.siteTopology (Type w))
variable (Gs : G → Sheaf Y.siteTopology (Type w))

/- Lemma 18.7.2 (03CR) (7): prescribed source and target families can simultaneously become
representable on the replacement sites. -/
@[stacks 03CR "(7)"]
#check (existsSiteReductionRepresenting f Fs Gs :
  ∃ R : SiteReduction f, SiteReduction.Represents (f := f) R Fs Gs)

section Equivalence

variable [f.IsEquivalence]

/- Lemma 18.7.2 (03CR), moreover: a ringed equivalence admits one common replacement site and
structure sheaf, with identity middle morphism. -/
@[stacks 03CR "equivalence"]
#check (existsCommonReduction f : Nonempty (CommonReduction f))

variable (S : CommonReduction f)

#check (S.site : RingedSite.{u, v, w})
#check (S.sourceComparison : ToposHom X S.site)
#check (S.targetComparison : ToposHom Y S.site)
#check (S.middle : S.site ⟶ S.site)

/- The common-site specialization can retain the prescribed representable families. -/
#check (existsCommonReductionRepresenting f Fs Gs :
  ∃ S : CommonReduction f, CommonReduction.Represents (f := f) S Fs Gs)

end Equivalence

end RingedSite.ToposHom
