/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.Ring.Colimits
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.Algebra.Category.Ring.Sheaf.Point
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Stalks of modules at points of a ringed site

This file owns the module-valued stalk functors attached to a point of an arbitrary Grothendieck
topology.  In particular, none of the constructions depend on a topological-space realization of
the site.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u v w

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
variable {J : GrothendieckTopology C}
variable (p : GrothendieckTopology.Point.{w} J)
variable (𝒪 : Sheaf J RingCat.{w})

/-- The coefficient ring obtained by taking the fiber of a ring sheaf at a site point. -/
@[stacks 04EQ "ring-valued stalk"]
abbrev stalkRing : RingCat.{w} :=
  p.presheafFiber.obj 𝒪.obj

/-- The stalk functor from presheaves of `𝒪`-modules to modules over `𝒪ₚ`. -/
@[stacks 04EQ "module-presheaf stalk functor"]
abbrev presheafModuleStalkFunctor :
    PresheafOfModules 𝒪.obj ⥤ ModuleCat (p.stalkRing 𝒪) :=
  PresheafOfModules.pushforward₀ (CategoryOfElements.π p.fiber) 𝒪.obj ⋙
    PresheafOfModules.colimitFunctor (p.isColimitPresheafFiberCocone 𝒪.obj)

/-- The stalk functor from sheaves of `𝒪`-modules to modules over `𝒪ₚ`. -/
@[stacks 04EQ "module-sheaf stalk functor"]
abbrev sheafModuleStalkFunctor :
    SheafOfModules 𝒪 ⥤ ModuleCat (p.stalkRing 𝒪) :=
  SheafOfModules.forget 𝒪 ⋙ p.presheafModuleStalkFunctor 𝒪

/-- Lemma 18.36.3 (1): the stalk functor on sheaves of modules over a ringed site is exact. -/
@[stacks 04EQ "(1)"]
theorem sheafModuleStalk_exact :
    exactFunctor (SheafOfModules 𝒪) (ModuleCat (p.stalkRing 𝒪))
      (p.sheafModuleStalkFunctor 𝒪) := sorry

/-- Lemma 18.36.3 (2): the stalk functor on presheaves of modules over a ringed site is exact. -/
@[stacks 04EQ "(2)"]
theorem presheafModuleStalk_exact :
    exactFunctor (PresheafOfModules 𝒪.obj) (ModuleCat (p.stalkRing 𝒪))
      (p.presheafModuleStalkFunctor 𝒪) := sorry

/-- The stalk functor on module sheaves over a ring sheaf is additive. -/
@[stacks 04EQ "additivity of module-sheaf stalks"]
instance sheafModuleStalkFunctor_additive :
    (p.sheafModuleStalkFunctor 𝒪).Additive := sorry

/-- A site-point stalk functor on module sheaves preserves all colimits whenever additive
sheafification is available. -/
noncomputable instance sheafModuleStalkFunctorPreservesColimits
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] :
    PreservesColimits (p.sheafModuleStalkFunctor 𝒪) := sorry

section Sheafification

variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The canonical morphism from the stalk of a module presheaf to the stalk of its
sheafification. -/
noncomputable def presheafModuleStalkToSheafification_hom
    (F : PresheafOfModules 𝒪.obj) :
    (p.presheafModuleStalkFunctor 𝒪).obj F ⟶
      (PresheafOfModules.sheafification (𝟙 𝒪.obj) ⋙
        p.sheafModuleStalkFunctor 𝒪).obj F :=
  (p.presheafModuleStalkFunctor 𝒪).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 𝒪.obj)).unit.app F) ≫
    (ModuleCat.restrictScalarsId (p.stalkRing 𝒪)).hom.app
      ((p.sheafModuleStalkFunctor 𝒪).obj
        ((PresheafOfModules.sheafification (𝟙 𝒪.obj)).obj F))

/-- The canonical stalk-to-sheafification morphisms are natural in the module presheaf. -/
theorem presheafModuleStalkToSheafification_naturality
    {F G : PresheafOfModules 𝒪.obj} (f : F ⟶ G) :
    (p.presheafModuleStalkFunctor 𝒪).map f ≫
        p.presheafModuleStalkToSheafification_hom 𝒪 G =
      p.presheafModuleStalkToSheafification_hom 𝒪 F ≫
        (PresheafOfModules.sheafification (𝟙 𝒪.obj) ⋙
          p.sheafModuleStalkFunctor 𝒪).map f := sorry

/-- The canonical natural transformation from module-presheaf stalks to sheafified stalks. -/
noncomputable def presheafModuleStalkToSheafification :
    p.presheafModuleStalkFunctor 𝒪 ⟶
      PresheafOfModules.sheafification (𝟙 𝒪.obj) ⋙
        p.sheafModuleStalkFunctor 𝒪 where
  app F := p.presheafModuleStalkToSheafification_hom 𝒪 F
  naturality _ _ f := p.presheafModuleStalkToSheafification_naturality 𝒪 f

/-- Lemma 18.36.3 (3): the canonical natural transformation from module-presheaf stalks to
sheafified module stalks is invertible.  Keeping the forward transformation as the data owner
avoids selecting inverse data from a deferred `IsIso` proof. -/
@[stacks 04EQ "(3)"]
noncomputable instance presheafModuleStalkToSheafification_isIso :
    IsIso (p.presheafModuleStalkToSheafification 𝒪) := sorry

end Sheafification

end CategoryTheory.GrothendieckTopology.Point

namespace CategoryTheory.GrothendieckTopology.Point

open SheafOfModules.RingedSite

universe uC vC

variable {C : Type uC} [Category.{vC} C] [LocallySmall.{w} C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The stalk of the underlying ring sheaf is canonically the underlying ring of the
commutative-ring-valued stalk. -/
@[stacks 04EQ "commutative stalk-ring comparison"]
noncomputable abbrev stalkRingEquiv
    (p : Point.{w} J) (O : Sheaf J CommRingCat.{w}) :
    p.stalkRing (ringSheaf J O) ≃+* p.stalkCommRing O :=
  ((p.presheafFiberCompIso (forget₂ CommRingCat.{w} RingCat.{w})).app
    O.obj).ringCatIsoToRingEquiv

/-- The module-valued stalk functor at a site point, with coefficient and module universe
independent of the site's object and morphism universes. -/
@[stacks 04EQ "universe-polymorphic module stalk functor"]
noncomputable abbrev moduleStalkFunctor
    (p : Point.{w} J) (O : Sheaf J CommRingCat.{w}) :
    ringedSiteModuleCategory.{uC, vC, w, w} J O ⥤
      ModuleCat.{w} (p.stalkCommRing O) :=
  p.sheafModuleStalkFunctor (ringSheaf J O) ⋙
    ModuleCat.restrictScalars (p.stalkRingEquiv O).symm.toRingHom

/-- The commutative-ring-valued module stalk functor is exact. -/
@[stacks 04EQ "exactness of commutative ringed-site module stalks"]
theorem moduleStalkFunctor_exact
    (p : Point.{w} J) (O : Sheaf J CommRingCat.{w}) :
    exactFunctor (ringedSiteModuleCategory.{uC, vC, w, w} J O)
      (ModuleCat.{w} (p.stalkCommRing O)) (p.moduleStalkFunctor O) := sorry

/-- The commutative-ring-valued module stalk functor is additive. -/
@[stacks 04EQ "additivity of commutative ringed-site module stalks"]
instance moduleStalkFunctor_additive
    (p : Point.{w} J) (O : Sheaf J CommRingCat.{w}) :
    (p.moduleStalkFunctor O).Additive := sorry

/-- The commutative-ring-valued module stalk functor preserves finite limits. -/
@[stacks 04EQ "finite-limit preservation by module stalks"]
instance moduleStalkFunctor_preservesFiniteLimits
    (p : Point.{w} J) (O : Sheaf J CommRingCat.{w}) :
    PreservesFiniteLimits (p.moduleStalkFunctor O) := sorry

/-- The commutative-ring-valued module stalk functor preserves finite colimits. -/
@[stacks 04EQ "finite-colimit preservation by module stalks"]
instance moduleStalkFunctor_preservesFiniteColimits
    (p : Point.{w} J) (O : Sheaf J CommRingCat.{w}) :
    PreservesFiniteColimits (p.moduleStalkFunctor O) := sorry

/-- The stalk of a module sheaf, retaining its canonical module structure over the
commutative-ring-valued stalk. -/
@[stacks 04EQ "universe-polymorphic module stalk"]
noncomputable abbrev moduleStalk
    (p : Point.{w} J) (O : Sheaf J CommRingCat.{w})
    (M : ringedSiteModuleCategory.{uC, vC, w, w} J O) :
    ModuleCat.{w} (p.stalkCommRing O) :=
  (p.moduleStalkFunctor O).obj M

end CategoryTheory.GrothendieckTopology.Point

-- Any `sorryAx` in the natural transformation itself is confined to its naturality proof field.
