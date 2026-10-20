module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Basic
public import ReasLib.CategoryTheory.Sites.Topos.Sections
public import Mathlib.CategoryTheory.Limits.Types.Limits

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe uX vX uY vY w

namespace RingedSite.ToposHom

/-- Forgetting ring structure preserves a sheaf's limiting cone even when
the site-object and site-morphism universes are different. -/
noncomputable instance ringForgetPreservesLimit
    {C : Type uX} [Category.{vX} C] {J : GrothendieckTopology C}
    [UnivLE.{uX, w}] (R : Sheaf J RingCat.{w}) :
    PreservesLimit R.obj (forget RingCat.{w}) :=
  preservesLimit_of_preserves_limit_cone (RingCat.limitConeIsLimit R.obj)
    (Types.Small.limitConeIsLimit (R.obj ⋙ forget RingCat.{w}))

/-- The underlying elements of the ring limit are compatible sections of its
underlying type-valued presheaf. -/
noncomputable def ringSectionsEquiv
    {C : Type uX} [Category.{vX} C] {J : GrothendieckTopology C}
    [UnivLE.{uX, w}] (R : Sheaf J RingCat.{w}) :
    (limit R.obj : RingCat.{w}) ≃ (R.obj ⋙ forget RingCat.{w}).sections :=
  (preservesLimitIso (forget RingCat.{w}) R.obj).toEquiv.trans
    (Types.limitEquivSections (R.obj ⋙ forget RingCat.{w}))

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
  [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{uX, w}] [UnivLE.{uY, w}]
variable (f : ToposHom X Y)

/-- The ring direct-image comparison on compatible families, followed by the
canonical topos global-section equivalence. -/
noncomputable def ringPushforwardSectionsEquiv :
    ((f.toTopos.ringDirectImage.obj X.structureSheaf).obj ⋙
      forget RingCat.{w}).sections ≃
        (X.structureSheaf.obj ⋙ forget RingCat.{w}).sections :=
  ((Functor.sectionsFunctor _).mapIso
    ((sheafToPresheaf Y.siteTopology (Type w)).mapIso
      (f.toTopos.ringDirectImageForgetIso.app X.structureSheaf))).toEquiv.trans
    (f.toTopos.pushforwardSectionsEquiv (Hom.underlyingStructureSheaf X))

/-- The map on global sections induced by a ringed-topos morphism, built from
its direct structure map and the canonical sections equivalence. -/
noncomputable def globalSectionsMap :
    Hom.globalSectionsRing Y ⟶ Hom.globalSectionsRing X :=
  RingCat.ofHom
    { toFun := fun s ↦ (ringSectionsEquiv X.structureSheaf).symm
        (f.ringPushforwardSectionsEquiv
          (ringSectionsEquiv (f.toTopos.ringDirectImage.obj X.structureSheaf)
            (lim.map f.directStructureMap.hom s)))
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry }

end RingedSite.ToposHom
