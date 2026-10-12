/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.StructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ringed
public import ReasLib.AlgebraicGeometry.Scheme.Sites.LiftedStructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.RingedTopos
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.RingedTopos
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u uC vC uD vD

section Generic

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

/- Remark 35.8.4 (1): every previously established morphism of sites whose realizations are
related by a scheme projection becomes a morphism of ringed sites. -/
@[stacks 070R] #check
  (AlgebraicGeometry.Scheme.Site.ringedHom :
    ∀ (J : GrothendieckTopology C) (K : GrothendieckTopology D)
      (P : C ⥤ Scheme.{u}) (Q : D ⥤ Scheme.{u}) (F : C ⥤ D)
      [IsMorphismOfSites J K F] (_ : F ⋙ Q ⟶ P)
      (hP : Presheaf.IsSheaf J (AlgebraicGeometry.Scheme.Site.structurePresheaf P))
      (hQ : Presheaf.IsSheaf K (AlgebraicGeometry.Scheme.Site.structurePresheaf Q)),
      RingedSite.Hom
        (RingedSite.ofRingSheaf K
          (⟨AlgebraicGeometry.Scheme.Site.structurePresheaf Q, hQ⟩ :
            Sheaf K RingCat.{u}))
        (RingedSite.ofRingSheaf J
          (⟨AlgebraicGeometry.Scheme.Site.structurePresheaf P, hP⟩ :
            Sheaf J RingCat.{u})))

/- Remark 35.8.4 (2): the underlying functor of the induced ringed-site morphism is the
given morphism of sites. -/
@[stacks 070R] #check
  (AlgebraicGeometry.Scheme.Site.ringedHom_base :
    ∀ (J : GrothendieckTopology C) (K : GrothendieckTopology D)
      (P : C ⥤ Scheme.{u}) (Q : D ⥤ Scheme.{u}) (F : C ⥤ D)
      [IsMorphismOfSites J K F] (projection : F ⋙ Q ⟶ P)
      (hP : Presheaf.IsSheaf J (AlgebraicGeometry.Scheme.Site.structurePresheaf P))
      (hQ : Presheaf.IsSheaf K (AlgebraicGeometry.Scheme.Site.structurePresheaf Q)),
      (AlgebraicGeometry.Scheme.Site.ringedHom
        J K P Q F projection hP hQ).base = F)

/- Remark 35.8.4 (3): objectwise, the projection-induced structure map is pullback on global
sections. -/
@[stacks 070R] #check
  (AlgebraicGeometry.Scheme.Site.ringedHom_structureSheafMap_app :
    ∀ (J : GrothendieckTopology C) (K : GrothendieckTopology D)
      (P : C ⥤ Scheme.{u}) (Q : D ⥤ Scheme.{u}) (F : C ⥤ D)
      [IsMorphismOfSites J K F] (projection : F ⋙ Q ⟶ P)
      (hP : Presheaf.IsSheaf J (AlgebraicGeometry.Scheme.Site.structurePresheaf P))
      (hQ : Presheaf.IsSheaf K (AlgebraicGeometry.Scheme.Site.structurePresheaf Q))
      (U : Cᵒᵖ),
      (AlgebraicGeometry.Scheme.Site.ringedHom
        J K P Q F projection hP hQ).structureSheafMap.hom.app U =
        RingCat.ofHom (projection.app U.unop).appTop.hom)

end Generic

section RingedSites

variable {S T : Scheme.{u}}

/- Remark 35.8.4 (4): every previously established pullback morphism between standard big
scheme sites becomes a morphism of ringed sites. -/
@[stacks 070R] #check
  (AlgebraicGeometry.StandardTopology.Big.ringedHom :
    ∀ (τ τ' : StandardTopology) (f : T ⟶ S)
      [IsMorphismOfSites (τ'.overTopology S) (τ.overTopology T) (Over.pullback f)],
      RingedSite.Hom
        (AlgebraicGeometry.StandardTopology.Big.ringedSite τ T)
        (AlgebraicGeometry.StandardTopology.Big.ringedSite τ' S))

/- Remark 35.8.4 (5): a scheme morphism induces a morphism of small étale ringed sites. -/
@[stacks 070R] #check
  (AlgebraicGeometry.Scheme.Etale.Small.ringedHom :
    (T ⟶ S) →
      RingedSite.Hom
        (AlgebraicGeometry.Scheme.Etale.Small.ringedSite T)
        (AlgebraicGeometry.Scheme.Etale.Small.ringedSite S))

/- Remark 35.8.4 (6): a scheme morphism induces a morphism of small Zariski ringed sites. -/
@[stacks 070R] #check
  (AlgebraicGeometry.Scheme.Zariski.Small.ringedHom :
    (T ⟶ S) →
      RingedSite.Hom
        (AlgebraicGeometry.Scheme.Zariski.Small.ringedSite T)
        (AlgebraicGeometry.Scheme.Zariski.Small.ringedSite S))

end RingedSites

section EtaleRingedTopos

variable {S T : Scheme.{u}}

/- Remark 35.8.4 (7): small-to-big étale relocalization is canonically a morphism of
ringed topoi. -/
@[stacks 070R] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.ringedToposHom :
    (T ⟶ S) →
      RingedSite.ToposHom
        (AlgebraicGeometry.Scheme.Etale.Small.liftedRingedSite T)
        (AlgebraicGeometry.StandardTopology.Big.liftedRingedSite .etale S))

/- Remark 35.8.4 (8): the underlying morphism of topoi identifies the small-to-big étale
ringed topos with the cited relocalization morphism. -/
@[stacks 070R] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.ringedToposHom_toTopos :
    ∀ f : T ⟶ S,
      (AlgebraicGeometry.Scheme.Etale.SmallToBig.ringedToposHom f).toTopos =
        AlgebraicGeometry.Scheme.Etale.SmallToBig.morphismOfTopoi f)

/- Remark 35.8.4 (9): for the small-to-big étale morphism, inverse image carries the big
structure sheaf isomorphically to the small structure sheaf. -/
@[stacks 070R] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.ringedToposHom_structureMap_isIso :
    ∀ f : T ⟶ S,
      IsIso (AlgebraicGeometry.Scheme.Etale.SmallToBig.ringedToposHom f).structureMap)

end EtaleRingedTopos

section ZariskiRingedTopos

variable {S T : Scheme.{u}}

/- Remark 35.8.4 (10): small-to-big Zariski relocalization is canonically a morphism of
ringed topoi. -/
@[stacks 070R] #check
  (AlgebraicGeometry.Scheme.Zariski.SmallToBig.ringedToposHom :
    (T ⟶ S) →
      RingedSite.ToposHom
        (AlgebraicGeometry.Scheme.Zariski.Small.liftedRingedSite T)
        (AlgebraicGeometry.StandardTopology.Big.liftedRingedSite .zariski S))

/- Remark 35.8.4 (11): the underlying morphism of topoi identifies the small-to-big Zariski
ringed topos with the cited relocalization morphism. -/
@[stacks 070R] #check
  (AlgebraicGeometry.Scheme.Zariski.SmallToBig.ringedToposHom_toTopos :
    ∀ f : T ⟶ S,
      (AlgebraicGeometry.Scheme.Zariski.SmallToBig.ringedToposHom f).toTopos =
        AlgebraicGeometry.Scheme.Zariski.SmallToBig.morphismOfTopoi f)

/- Remark 35.8.4 (12): for the small-to-big Zariski morphism, inverse image carries the big
structure sheaf isomorphically to the small structure sheaf. -/
@[stacks 070R] #check
  (AlgebraicGeometry.Scheme.Zariski.SmallToBig.ringedToposHom_structureMap_isIso :
    ∀ f : T ⟶ S,
      IsIso
        (AlgebraicGeometry.Scheme.Zariski.SmallToBig.ringedToposHom f).structureMap)

end ZariskiRingedTopos
