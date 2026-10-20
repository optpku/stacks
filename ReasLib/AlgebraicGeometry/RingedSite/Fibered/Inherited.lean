/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Basic
public import ReasLib.CategoryTheory.Fibered.InheritedTopology

/-!
# Inherited Ringed Sites

This leaf equips an inherited topology along a continuous functor into a
ringed site with the induced structure sheaf.  Although fibred categories are
the main application, the construction itself uses only the projection
functor and therefore belongs at the functor level.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory

namespace Functor

section

variable {X : RingedSite.{u, v, max u v}} {S : Type u} [Category.{v} S]

/-- The ring-valued sheaf on the topology inherited along `p`, obtained by
pushing forward the structure sheaf of the target ringed site. -/
@[stacks 08P8 "inherited structure sheaf"]
abbrev inheritedStructureSheaf
    (p : S ⥤ X.carrier)
    [p.IsContinuous (p.inheritedTopology X.siteTopology) X.siteTopology] :
    Sheaf (p.inheritedTopology X.siteTopology) RingCat.{max u v} :=
  (p.sheafPushforwardContinuous RingCat.{max u v}
    (p.inheritedTopology X.siteTopology) X.siteTopology).obj X.structureSheaf

/-- The ringed site on the topology inherited along `p`, with structure sheaf
`p.inheritedStructureSheaf`. -/
@[stacks 08P8 "inherited ringed site"]
abbrev inheritedRingedSite
    (p : S ⥤ X.carrier)
    [p.IsContinuous (p.inheritedTopology X.siteTopology) X.siteTopology] :
    RingedSite.{u, v, max u v} :=
  RingedSite.ofRingSheaf
    (p.inheritedTopology X.siteTopology)
    (p.inheritedStructureSheaf)

/-- The topology of `p.inheritedRingedSite` is the topology inherited along
`p`. -/
@[simp] theorem inheritedRingedSite_siteTopology
    (p : S ⥤ X.carrier)
    [p.IsContinuous (p.inheritedTopology X.siteTopology) X.siteTopology] :
    p.inheritedRingedSite.siteTopology = p.inheritedTopology X.siteTopology := sorry

/-- The structure sheaf of `p.inheritedRingedSite` is
`p.inheritedStructureSheaf`. -/
@[simp] theorem inheritedRingedSite_structureSheaf
    (p : S ⥤ X.carrier)
    [p.IsContinuous (p.inheritedTopology X.siteTopology) X.siteTopology] :
    p.inheritedRingedSite.structureSheaf = p.inheritedStructureSheaf := sorry

end

section

variable {X : RingedSite.{u, v, max u v}} {S : Type u} [Category.{v} S]

/-- The canonical morphism from `X` to the ringed site induced along `p`. -/
@[stacks 08P8 "inherited projection ringed-site morphism"]
abbrev inheritedProjectionRingedSiteHom
    (p : S ⥤ X.carrier)
    [hSite : IsMorphismOfSites (p.inheritedTopology X.siteTopology) X.siteTopology p] :
    RingedSite.Hom X p.inheritedRingedSite where
  base := p
  isMorphismOfSites := hSite
  structureSheafMap := 𝟙 p.inheritedStructureSheaf

/-- The base functor of `p.inheritedProjectionRingedSiteHom` is `p`. -/
@[simp] theorem inheritedProjectionRingedSiteHom_base
    (p : S ⥤ X.carrier)
    [IsMorphismOfSites (p.inheritedTopology X.siteTopology) X.siteTopology p] :
    p.inheritedProjectionRingedSiteHom.base = p := sorry

/-- The structure-sheaf map of `p.inheritedProjectionRingedSiteHom` is the
identity of the inherited structure sheaf. -/
@[simp] theorem inheritedProjectionRingedSiteHom_structureSheafMap
    (p : S ⥤ X.carrier)
    [IsMorphismOfSites (p.inheritedTopology X.siteTopology) X.siteTopology p] :
    p.inheritedProjectionRingedSiteHom.structureSheafMap = 𝟙 p.inheritedStructureSheaf := sorry

end

end Functor

end CategoryTheory
