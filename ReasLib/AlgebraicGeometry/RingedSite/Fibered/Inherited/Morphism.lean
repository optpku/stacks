/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Fibered.Inherited
public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Morphism
public import ReasLib.CategoryTheory.Sites.Topos.Morphism

/-!
# Morphisms of Inherited Ringed Sites

This leaf constructs the ringed-site morphism induced by a strictly commuting
triangle of functors into a common ringed site.  The data construction is
generic; fibred-category applications obtain the required triangle from their
projection functors.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory

namespace Functor

section

variable {D : RingedSite.{u, v}}
variable {S S' : Type u} [Category.{v} S] [Category.{v} S']
variable {p : S ⥤ D} {p' : S' ⥤ D}

/-- The canonical comparison from the inherited structure sheaf along `p'`
to the direct image of the inherited structure sheaf along `p`, for a
strictly commuting triangle `u ⋙ p = p'`. -/
@[stacks 08PA "inherited structure-sheaf comparison"]
def inheritedStructureSheafComparison
    (u : S' ⥤ S) (hcomm : u ⋙ p = p')
    [hp' : p'.IsContinuous (p'.inheritedTopology D.siteTopology) D.siteTopology]
    [hp : p.IsContinuous (p.inheritedTopology D.siteTopology) D.siteTopology]
    [hSite : IsMorphismOfSites
      (p'.inheritedTopology D.siteTopology)
      (p.inheritedTopology D.siteTopology)
      u] :
    p'.inheritedStructureSheaf ⟶
      (u.sheafPushforwardContinuous RingCat.{max u v}
        (p'.inheritedTopology D.siteTopology)
        (p.inheritedTopology D.siteTopology)).obj p.inheritedStructureSheaf :=
  let _ : p'.IsContinuous (p'.inheritedTopology D.siteTopology) D.siteTopology := hp'
  let _ : p.IsContinuous (p.inheritedTopology D.siteTopology) D.siteTopology := hp
  let _ : u.IsContinuous
      (p'.inheritedTopology D.siteTopology)
      (p.inheritedTopology D.siteTopology) := hSite.toIsContinuous
  let e := Functor.sheafPushforwardContinuousComp'
    (eqToIso hcomm)
    RingCat.{max u v}
    (p'.inheritedTopology D.siteTopology)
    (p.inheritedTopology D.siteTopology)
    D.siteTopology
  (e.symm.app D.structureSheaf).hom

/-- The morphism of ringed sites induced by a strictly commuting triangle of
functors into a common ringed site. -/
@[stacks 08PA "inherited ringed-site morphism"]
def inheritedRingedSiteHom
    (u : S' ⥤ S) (hcomm : u ⋙ p = p')
    [hp' : p'.IsContinuous (p'.inheritedTopology D.siteTopology) D.siteTopology]
    [hp : p.IsContinuous (p.inheritedTopology D.siteTopology) D.siteTopology]
    [hSite : IsMorphismOfSites
      (p'.inheritedTopology D.siteTopology)
      (p.inheritedTopology D.siteTopology)
      u] :
    p.inheritedRingedSite ⟶ p'.inheritedRingedSite where
  base := u
  isMorphismOfSites := hSite
  structureSheafMap := inheritedStructureSheafComparison u hcomm

variable (u : S' ⥤ S) (hcomm : u ⋙ p = p')
variable [p'.IsContinuous (p'.inheritedTopology D.siteTopology) D.siteTopology]
variable [p.IsContinuous (p.inheritedTopology D.siteTopology) D.siteTopology]
variable [IsMorphismOfSites
  (p'.inheritedTopology D.siteTopology)
  (p.inheritedTopology D.siteTopology)
  u]

/-- The base functor of the inherited-ringed-site morphism is `u`. -/
@[simp] theorem inheritedRingedSiteHom_base :
    RingedSite.Hom.base (inheritedRingedSiteHom u hcomm) = u := sorry

/-- The structure-sheaf map of `inheritedRingedSiteHom u hcomm` is the
canonical comparison map. -/
@[simp] theorem inheritedRingedSiteHom_structureSheafMap :
    (inheritedRingedSiteHom u hcomm).structureSheafMap =
      inheritedStructureSheafComparison u hcomm := sorry

end

section

variable {D : RingedSite.{u, v}}
variable {S S' : Type u} [Category.{v} S] [Category.{v} S']
variable {p : S ⥤ D} {p' : S' ⥤ D}
variable (u : S' ⥤ S) (hcomm : u ⋙ p = p')
variable [IsMorphismOfSites (p'.inheritedTopology D.siteTopology) D.siteTopology p']
variable [IsMorphismOfSites (p.inheritedTopology D.siteTopology) D.siteTopology p]
variable [IsMorphismOfSites
  (p'.inheritedTopology D.siteTopology)
  (p.inheritedTopology D.siteTopology)
  u]

/-- The ringed-site morphism of a strictly commuting triangle is compatible
with the canonical projections to its common base ringed site. -/
@[stacks 08PA "commutative triangle of inherited ringed sites"]
theorem inheritedRingedSiteHom_projection :
    CommSq
      p.inheritedProjectionRingedSiteHom
      p'.inheritedProjectionRingedSiteHom
      (inheritedRingedSiteHom u hcomm)
      (𝟙 p'.inheritedRingedSite) := sorry

/-- Projection compatibility of `inheritedRingedSiteHom u hcomm` as an
equality of ringed-site morphisms. -/
@[stacks 08PA "projection composition law", simp]
theorem inheritedRingedSiteHom_projection_w :
    p.inheritedProjectionRingedSiteHom ≫ inheritedRingedSiteHom u hcomm =
      p'.inheritedProjectionRingedSiteHom := sorry

end

namespace inheritedProjectionRingedSiteHom

section

variable {D : RingedSite.{u, v}} {S : Type u} [Category.{v} S]
variable (p : S ⥤ D)
variable [IsMorphismOfSites (p.inheritedTopology D.siteTopology) D.siteTopology p]

/-- The localization of the inherited projection has the canonical continuous base functor.

This instance is stated at the inherited-ringed-site level, where the displayed topologies are
the ones used by downstream localized topos constructions. -/
@[stacks 08P8 "inherited localization continuity"]
instance localization_isContinuous (U : S) :
    (p.inheritedProjectionRingedSiteHom.localization U).base.IsContinuous
      (p.inheritedRingedSite.localization U).siteTopology
      (D.localization (p.obj U)).siteTopology := sorry

/-- Finite-limit preservation for the localized inherited projection, transferred from the
underlying slice projection. -/
@[stacks 08P8 "inherited localization finite limits"]
instance localization_preservesFiniteLimits (U : S)
    [PreservesFiniteLimits
      ((Over.post p).sheafPullback
        (Type (max u v))
        ((p.inheritedTopology D.siteTopology).over U)
        (D.siteTopology.over (p.obj U)))] :
    PreservesFiniteLimits
      ((p.inheritedProjectionRingedSiteHom.localization U).base.sheafPullback
        (Type (max u v))
        ((p.inheritedRingedSite.localization U).siteTopology)
        ((D.localization (p.obj U)).siteTopology)) := sorry

end

end inheritedProjectionRingedSiteHom

namespace inheritedRingedSiteHom

section

variable {D : RingedSite.{u, v}}
variable {S S' : Type u} [Category.{v} S] [Category.{v} S']
variable {p : S ⥤ D} {p' : S' ⥤ D}

/-- A strictly commuting inherited-site comparison has the expected equality on objects over
the common base. -/
@[stacks 08PB "inherited comparison projection on objects"]
theorem projection_obj (f : S' ⥤ S) (hcomm : f ⋙ p = p') (U : S') :
    p.obj (f.obj U) = p'.obj U := sorry

end

section

variable {D : RingedSite.{u, v}}
variable {S S' : Type u} [Category.{v} S] [Category.{v} S']
variable {p : S ⥤ D} {p' : S' ⥤ D}
variable (f : S' ⥤ S) (hcomm : f ⋙ p = p')
variable [IsMorphismOfSites (p'.inheritedTopology D.siteTopology) D.siteTopology p']
variable [IsMorphismOfSites (p.inheritedTopology D.siteTopology) D.siteTopology p]
variable [IsMorphismOfSites
  (p'.inheritedTopology D.siteTopology)
  (p.inheritedTopology D.siteTopology)
  f]

/-- The slice functor underlying an inherited-ringed-site comparison is continuous for the
localized inherited topologies. -/
@[stacks 08PB "inherited comparison slice continuity"]
instance overPost_isContinuous (U : S') :
    (Over.post (Functor.inheritedRingedSiteHom f hcomm).base).IsContinuous
      (p'.inheritedRingedSite.localization U).siteTopology
      (p.inheritedRingedSite.localization
        ((Functor.inheritedRingedSiteHom f hcomm).base.obj U)).siteTopology := sorry

/-- Finite-limit preservation for the slice functor underlying an inherited-ringed-site
comparison is transferred from the original comparison functor. -/
@[stacks 08PB "inherited comparison slice finite limits"]
instance overPost_preservesFiniteLimits (U : S')
    [PreservesFiniteLimits
      ((Over.post f).sheafPullback
        (Type (max u v))
        ((p'.inheritedTopology D.siteTopology).over U)
        ((p.inheritedTopology D.siteTopology).over (f.obj U)))] :
    PreservesFiniteLimits
      ((Over.post (Functor.inheritedRingedSiteHom f hcomm).base).sheafPullback
        (Type (max u v))
        (p'.inheritedRingedSite.localization U).siteTopology
        (p.inheritedRingedSite.localization
          ((Functor.inheritedRingedSiteHom f hcomm).base.obj U)).siteTopology) := sorry

/-- The localization of an inherited-ringed-site comparison is continuous. -/
@[stacks 08PB "inherited comparison localization continuity"]
instance localization_isContinuous (U : S') :
    ((Functor.inheritedRingedSiteHom f hcomm).localization U).base.IsContinuous
      (p'.inheritedRingedSite.localization U).siteTopology
      (p.inheritedRingedSite.localization
        ((Functor.inheritedRingedSiteHom f hcomm).base.obj U)).siteTopology := sorry

/-- The localization of an inherited-ringed-site comparison preserves finite limits whenever
the inverse image along the original slice comparison does. -/
@[stacks 08PB "inherited comparison localization finite limits"]
instance localization_preservesFiniteLimits (U : S')
    [PreservesFiniteLimits
      ((Over.post f).sheafPullback
        (Type (max u v))
        ((p'.inheritedTopology D.siteTopology).over U)
        ((p.inheritedTopology D.siteTopology).over (f.obj U)))] :
    PreservesFiniteLimits
      (((Functor.inheritedRingedSiteHom f hcomm).localization U).base.sheafPullback
        (Type (max u v))
        (p'.inheritedRingedSite.localization U).siteTopology
        (p.inheritedRingedSite.localization
          ((Functor.inheritedRingedSiteHom f hcomm).base.obj U)).siteTopology) := sorry

end

end inheritedRingedSiteHom

end Functor

end CategoryTheory
