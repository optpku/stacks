/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Functor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections.Restriction
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Adjunction for associated module sheaves

The associated-module functor is left adjoint to module-valued global sections with scalars
restricted along `alpha : R →+* Γ(X, O_X)`. The identity-scalar specialization recovers ordinary
global sections.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Associated

variable {X : RingedSpace.{u}} {R : Type u} [CommRing R]

/-- The geometric right adjoint: push a module sheaf to the ringed point and evaluate it on the
top open. -/
noncomputable def geometricSectionsFunctor (alpha : R →+* X.globalSectionsRing) :
    X.Modules ⥤ ModuleCat.{u} R :=
  RingedSpace.Hom.pushforward (pointMap alpha) ⋙ RingedPoint.Module.topSectionsFunctor R

/-- The canonical adjunction between the associated-module functor and the geometric
pushforward-and-evaluation model of global sections. -/
noncomputable def geometricAdjunction (alpha : R →+* X.globalSectionsRing) :
    functor alpha ⊣ geometricSectionsFunctor alpha :=
  (RingedPoint.Module.equivalence R).toAdjunction.comp
    (RingedSpace.Hom.pullbackPushforwardAdjunction (pointMap alpha))

/-- The identity additive map intertwines the two scalar actions on the geometric and ordinary
global-sections models. -/
@[stacks 01BH "global sections comparison linearity"]
theorem geometricSectionsIsoApp_smul (alpha : R →+* X.globalSectionsRing) (G : X.Modules)
    (r : R) :
    (Iso.refl _).hom ≫ (RingedSpace.moduleGlobalSectionsRestriction X alpha G).smul r =
      ((geometricSectionsFunctor alpha).obj G).smul r ≫ (Iso.refl _).hom := sorry

/-- The geometric right adjoint agrees objectwise with ordinary global sections restricted along
`alpha`. -/
@[stacks 01BH "global sections comparison component"]
noncomputable def geometricSectionsIsoApp (alpha : R →+* X.globalSectionsRing) (G : X.Modules) :
    (geometricSectionsFunctor alpha).obj G ≅
      RingedSpace.moduleGlobalSectionsRestriction X alpha G :=
  ModuleCat.isoMk (Iso.refl _) (geometricSectionsIsoApp_smul alpha G)

/-- The objectwise comparison between the two global-sections models is natural. -/
@[reassoc, stacks 01BH "global sections comparison naturality"]
theorem geometricSectionsIsoApp_naturality (alpha : R →+* X.globalSectionsRing)
    {G H : X.Modules} (f : G ⟶ H) :
    (geometricSectionsFunctor alpha).map f ≫ (geometricSectionsIsoApp alpha H).hom =
      (geometricSectionsIsoApp alpha G).hom ≫
        (RingedSpace.moduleGlobalSectionsRestrictionFunctor X alpha).map f := sorry

/-- The inverses of the objectwise global-sections comparisons are natural. -/
@[reassoc, stacks 01BH "inverse global sections comparison naturality"]
theorem geometricSectionsIsoAppInv_naturality (alpha : R →+* X.globalSectionsRing)
    {G H : X.Modules} (f : G ⟶ H) :
    (RingedSpace.moduleGlobalSectionsRestrictionFunctor X alpha).map f ≫
        (geometricSectionsIsoApp alpha H).inv =
      (geometricSectionsIsoApp alpha G).inv ≫
        (geometricSectionsFunctor alpha).map f := sorry

/-- The objectwise global-sections comparisons form the forward natural transformation. -/
@[stacks 01BH "global sections comparison natural transformation"]
noncomputable def geometricSectionsNatTrans (alpha : R →+* X.globalSectionsRing) :
    geometricSectionsFunctor alpha ⟶
      RingedSpace.moduleGlobalSectionsRestrictionFunctor X alpha where
  app G := (geometricSectionsIsoApp alpha G).hom
  naturality _ _ f := geometricSectionsIsoApp_naturality alpha f

/-- The objectwise inverse global-sections comparisons form the inverse natural transformation. -/
@[stacks 01BH "inverse global sections comparison natural transformation"]
noncomputable def geometricSectionsInvNatTrans (alpha : R →+* X.globalSectionsRing) :
    RingedSpace.moduleGlobalSectionsRestrictionFunctor X alpha ⟶
      geometricSectionsFunctor alpha where
  app G := (geometricSectionsIsoApp alpha G).inv
  naturality _ _ f := geometricSectionsIsoAppInv_naturality alpha f

/-- A component of the forward global-sections comparison is the hom of the objectwise
comparison isomorphism. -/
@[simp, stacks 01BH "global sections comparison natural transformation component"]
theorem geometricSectionsNatTrans_app (alpha : R →+* X.globalSectionsRing)
    (G : X.Modules) :
    (geometricSectionsNatTrans alpha).app G = (geometricSectionsIsoApp alpha G).hom := sorry

/-- A component of the inverse global-sections comparison is the inverse of the objectwise
comparison isomorphism. -/
@[simp, stacks 01BH "inverse global sections comparison natural transformation component"]
theorem geometricSectionsInvNatTrans_app (alpha : R →+* X.globalSectionsRing)
    (G : X.Modules) :
    (geometricSectionsInvNatTrans alpha).app G =
      (geometricSectionsIsoApp alpha G).inv := sorry

/-- The forward global-sections comparison followed by its inverse is the identity. -/
@[simp, stacks 01BH "global sections comparison natural forward-inverse law"]
theorem geometricSectionsNatTrans_hom_inv_id
    (alpha : R →+* X.globalSectionsRing) :
    geometricSectionsNatTrans alpha ≫ geometricSectionsInvNatTrans alpha = 𝟙 _ := sorry

/-- The inverse global-sections comparison followed by the forward comparison is the identity. -/
@[simp, stacks 01BH "global sections comparison natural inverse-forward law"]
theorem geometricSectionsNatTrans_inv_hom_id
    (alpha : R →+* X.globalSectionsRing) :
    geometricSectionsInvNatTrans alpha ≫ geometricSectionsNatTrans alpha = 𝟙 _ := sorry

/-- Geometric pushforward to the ringed point followed by top evaluation is naturally isomorphic
to ordinary global sections with scalars restricted along `alpha`. -/
@[stacks 01BH "global sections comparison"]
noncomputable def geometricSectionsIso (alpha : R →+* X.globalSectionsRing) :
    geometricSectionsFunctor alpha ≅
      RingedSpace.moduleGlobalSectionsRestrictionFunctor X alpha where
  hom := geometricSectionsNatTrans alpha
  inv := geometricSectionsInvNatTrans alpha
  hom_inv_id := geometricSectionsNatTrans_hom_inv_id alpha
  inv_hom_id := geometricSectionsNatTrans_inv_hom_id alpha

/-- The forward natural transformation of `geometricSectionsIso` is the named comparison. -/
@[simp, stacks 01BH "global sections natural isomorphism hom"]
theorem geometricSectionsIso_hom (alpha : R →+* X.globalSectionsRing) :
    (geometricSectionsIso alpha).hom = geometricSectionsNatTrans alpha := sorry

/-- The inverse natural transformation of `geometricSectionsIso` is the named inverse
comparison. -/
@[simp, stacks 01BH "global sections natural isomorphism inverse"]
theorem geometricSectionsIso_inv (alpha : R →+* X.globalSectionsRing) :
    (geometricSectionsIso alpha).inv = geometricSectionsInvNatTrans alpha := sorry

/-- A component of `geometricSectionsIso` is the objectwise global-sections comparison
isomorphism. -/
@[simp, stacks 01BH "global sections natural isomorphism component"]
theorem geometricSectionsIso_app (alpha : R →+* X.globalSectionsRing) (G : X.Modules) :
    (geometricSectionsIso alpha).app G = geometricSectionsIsoApp alpha G := sorry

/-- A forward component of `geometricSectionsIso` is the hom of the objectwise comparison. -/
@[simp, stacks 01BH "global sections natural isomorphism hom component"]
theorem geometricSectionsIso_hom_app (alpha : R →+* X.globalSectionsRing)
    (G : X.Modules) :
    (geometricSectionsIso alpha).hom.app G =
      (geometricSectionsIsoApp alpha G).hom := sorry

/-- An inverse component of `geometricSectionsIso` is the inverse of the objectwise comparison. -/
@[simp, stacks 01BH "global sections natural isomorphism inverse component"]
theorem geometricSectionsIso_inv_app (alpha : R →+* X.globalSectionsRing)
    (G : X.Modules) :
    (geometricSectionsIso alpha).inv.app G =
      (geometricSectionsIsoApp alpha G).inv := sorry

/-- The associated-module functor is left adjoint to ordinary global sections with scalars
restricted along `alpha`. -/
@[stacks 01BH "(6)"]
noncomputable def adjunction (alpha : R →+* X.globalSectionsRing) :
    functor alpha ⊣ RingedSpace.moduleGlobalSectionsRestrictionFunctor X alpha :=
  (geometricAdjunction alpha).ofNatIsoRight (geometricSectionsIso alpha)

/-- The identity-scalar associated-module functor is left adjoint to ordinary global
sections. -/
@[stacks 01BH "identity scalar adjunction"]
noncomputable def idAdjunction (X : RingedSpace.{u}) :
    functor (RingHom.id X.globalSectionsRing) ⊣ X.moduleGlobalSectionsFunctor :=
  (adjunction (RingHom.id X.globalSectionsRing)).ofNatIsoRight
    (RingedSpace.moduleGlobalSectionsRestrictionFunctor.idIso X)

/-- Morphisms from an associated module sheaf are represented by `R`-linear maps into ordinary
global sections. -/
@[stacks 01BH "Hom equivalence"]
noncomputable abbrev homEquiv (alpha : R →+* X.globalSectionsRing)
    (M : ModuleCat.{u} R) (G : X.Modules) :
    (obj alpha M ⟶ G) ≃
      (M ⟶ RingedSpace.moduleGlobalSectionsRestriction X alpha G) :=
  (adjunction alpha).homEquiv M G

/-- Morphisms from an identity-scalar associated module sheaf are represented by maps into
ordinary global sections. -/
@[stacks 01BH "identity scalar Hom equivalence"]
noncomputable abbrev idHomEquiv (X : RingedSpace.{u})
    (M : ModuleCat.{u} X.globalSectionsRing) (G : X.Modules) :
    (obj (RingHom.id X.globalSectionsRing) M ⟶ G) ≃
      (M ⟶ X.moduleGlobalSectionsFunctor.obj G) :=
  (idAdjunction X).homEquiv M G

/-- The associated-module functor is a left adjoint. -/
noncomputable instance functor_isLeftAdjoint (alpha : R →+* X.globalSectionsRing) :
    (functor alpha).IsLeftAdjoint :=
  (adjunction alpha).isLeftAdjoint

/-- The associated-module functor preserves arbitrary colimits. -/
@[stacks 01BH "preserves colimits"]
noncomputable instance functor_preservesColimits (alpha : R →+* X.globalSectionsRing) :
    PreservesColimits (functor alpha) :=
  (adjunction alpha).leftAdjoint_preservesColimits

end AlgebraicGeometry.RingedSpace.Module.Associated
