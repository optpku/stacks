/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections.Stalk
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.PullbackStalk
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Point.Stalk
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stalks of associated module sheaves

The stalk comparison is the adjoint transpose of the composite from a module into the global
sections of its associated sheaf and then to the stalk. Its invertibility is packaged as a natural
isomorphism in the input module.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Associated

variable {X : RingedSpace.{u}} {R : Type u} [CommRing R]

/-- Extend an `R`-module to the local ring at `x` through the map from global scalars. -/
@[stacks 01BH "extension of scalars to an associated-sheaf stalk"]
noncomputable abbrev stalkExtensionFunctor
    (alpha : R →+* X.globalSectionsRing) (x : X) :
    ModuleCat.{u} R ⥤ ModuleCat.{u} (X.presheaf.stalk x) :=
  ModuleCat.extendScalars (X.globalSectionsToStalk alpha x)

/-- Form an associated module sheaf and then take its stalk at `x`. -/
@[stacks 01BH "associated-sheaf stalk functor"]
noncomputable abbrev stalkFunctor
    (alpha : R →+* X.globalSectionsRing) (x : X) :
    ModuleCat.{u} R ⥤ ModuleCat.{u} (X.presheaf.stalk x) :=
  functor alpha ⋙ X.stalkModuleFunctor x

/-- The stalk-ring map of the point morphism classified by `alpha`. -/
@[stacks 01BH "point-map stalk ring map"]
noncomputable abbrev pointStalkMap
    (alpha : R →+* X.globalSectionsRing) (x : X) :
    (RingedPoint.of R).presheaf.stalk RingedPoint.point →+* X.presheaf.stalk x :=
  ((pointMap alpha).hom.stalkMap x).hom

/-- The point-map stalk ring map factors the global-scalar map into the local ring. -/
@[stacks 01BH "point-map stalk factorization"]
theorem pointStalkMap_comp
    (alpha : R →+* X.globalSectionsRing) (x : X) :
    (pointStalkMap alpha x).comp (RingedPoint.stalkIso R).inv.hom =
      X.globalSectionsToStalk alpha x := sorry

/-- The canonical comparison from extension of scalars to the stalk of an associated module
sheaf. It is the extension/restriction adjoint transpose of the unit followed by the germ map. -/
@[stacks 01BH "associated-sheaf stalk comparison"]
noncomputable def stalkComparison
    (alpha : R →+* X.globalSectionsRing) (M : ModuleCat.{u} R) (x : X) :
    (stalkExtensionFunctor alpha x).obj M ⟶ (stalkFunctor alpha x).obj M :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (X.globalSectionsToStalk alpha x)
    ((adjunction alpha).unit.app M ≫
      X.moduleGlobalSectionsToStalk alpha (obj alpha M) x)

/-- The associated-sheaf stalk comparison is natural in the input module. -/
@[stacks 01BH "associated-sheaf stalk comparison naturality"]
theorem stalkComparison_naturality
    (alpha : R →+* X.globalSectionsRing) (x : X)
    {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (stalkExtensionFunctor alpha x).map f ≫ stalkComparison alpha N x =
      stalkComparison alpha M x ≫ (stalkFunctor alpha x).map f := sorry

/-- The inverse morphism of the associated-sheaf stalk comparison.  This named component is the
canonical inverse used by the objectwise and functorial stalk APIs below. -/
@[stacks 01BH "inverse associated-sheaf stalk comparison"]
noncomputable def stalkComparisonInv
    (alpha : R →+* X.globalSectionsRing) (M : ModuleCat.{u} R) (x : X) :
    (stalkFunctor alpha x).obj M ⟶ (stalkExtensionFunctor alpha x).obj M :=
  (RingedSpace.Hom.pullbackStalkIso (pointMap alpha)
      (RingedPoint.Module.sheaf R M) x).inv ≫
    (ModuleCat.extendScalars (pointStalkMap alpha x)).map
      (RingedPoint.Module.stalkModuleIso R M).inv ≫
    (ModuleCat.extendScalarsComp
      (RingedPoint.stalkIso R).inv.hom (pointStalkMap alpha x)).inv.app M ≫
    (eqToIso (congrArg
      (fun k : R →+* X.presheaf.stalk x ↦
        (ModuleCat.extendScalars k).obj M)
      (pointStalkMap_comp alpha x))).hom

/-- The associated-sheaf stalk comparison followed by its named inverse is the identity. -/
@[simp, stacks 01BH "associated-sheaf stalk comparison forward-inverse law"]
theorem stalkComparison_hom_inv_id
    (alpha : R →+* X.globalSectionsRing) (M : ModuleCat.{u} R) (x : X) :
    stalkComparison alpha M x ≫ stalkComparisonInv alpha M x = 𝟙 _ := sorry

/-- The named inverse followed by the associated-sheaf stalk comparison is the identity. -/
@[simp, stacks 01BH "associated-sheaf stalk comparison inverse-forward law"]
theorem stalkComparison_inv_hom_id
    (alpha : R →+* X.globalSectionsRing) (M : ModuleCat.{u} R) (x : X) :
    stalkComparisonInv alpha M x ≫ stalkComparison alpha M x = 𝟙 _ := sorry

/-- The associated-sheaf stalk comparison as literal isomorphism data. -/
@[stacks 01BH "associated-sheaf stalk comparison isomorphism"]
noncomputable def stalkComparisonIso
    (alpha : R →+* X.globalSectionsRing) (M : ModuleCat.{u} R) (x : X) :
    (stalkExtensionFunctor alpha x).obj M ≅ (stalkFunctor alpha x).obj M where
  hom := stalkComparison alpha M x
  inv := stalkComparisonInv alpha M x
  hom_inv_id := stalkComparison_hom_inv_id alpha M x
  inv_hom_id := stalkComparison_inv_hom_id alpha M x

/-- The canonical associated-sheaf stalk comparison is an isomorphism. -/
@[stacks 01BH "associated-sheaf stalk comparison is an isomorphism", instance]
noncomputable instance stalkComparison_isIso
    (alpha : R →+* X.globalSectionsRing) (M : ModuleCat.{u} R) (x : X) :
    IsIso (stalkComparison alpha M x) := sorry

/-- The forward map of `stalkComparisonIso` is the canonical comparison. -/
@[simp, stacks 01BH "associated-sheaf stalk comparison isomorphism hom"]
theorem stalkComparisonIso_hom
    (alpha : R →+* X.globalSectionsRing) (M : ModuleCat.{u} R) (x : X) :
    (stalkComparisonIso alpha M x).hom = stalkComparison alpha M x := sorry

/-- The inverse map of `stalkComparisonIso` is the named stalk comparison inverse. -/
@[simp, stacks 01BH "associated-sheaf stalk comparison isomorphism inverse"]
theorem stalkComparisonIso_inv
    (alpha : R →+* X.globalSectionsRing) (M : ModuleCat.{u} R) (x : X) :
    (stalkComparisonIso alpha M x).inv = stalkComparisonInv alpha M x := sorry

/-- The inverse stalk comparison is natural in the input module. -/
@[reassoc, stacks 01BH "associated-sheaf stalk inverse naturality"]
theorem stalkComparisonInv_naturality
    (alpha : R →+* X.globalSectionsRing) (x : X)
    {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (stalkFunctor alpha x).map f ≫ stalkComparisonInv alpha N x =
      stalkComparisonInv alpha M x ≫ (stalkExtensionFunctor alpha x).map f := sorry

/-- The associated-sheaf stalk comparisons form a natural transformation in the input
module. -/
@[stacks 01BH "associated-sheaf stalk natural transformation"]
noncomputable def stalkFunctorNatTrans
    (alpha : R →+* X.globalSectionsRing) (x : X) :
    stalkExtensionFunctor alpha x ⟶ stalkFunctor alpha x where
  app M := stalkComparison alpha M x
  naturality _ _ f := stalkComparison_naturality alpha x f

/-- The named inverse associated-sheaf stalk comparisons form a natural transformation in the
input module. -/
@[stacks 01BH "inverse associated-sheaf stalk natural transformation"]
noncomputable def stalkFunctorInvNatTrans
    (alpha : R →+* X.globalSectionsRing) (x : X) :
    stalkFunctor alpha x ⟶ stalkExtensionFunctor alpha x where
  app M := stalkComparisonInv alpha M x
  naturality _ _ f := stalkComparisonInv_naturality alpha x f

/-- The associated-sheaf stalk comparison transformation followed by its named inverse is the
identity. -/
@[simp, stacks 01BH "associated-sheaf stalk natural forward-inverse law"]
theorem stalkFunctorNatTrans_hom_inv_id
    (alpha : R →+* X.globalSectionsRing) (x : X) :
    stalkFunctorNatTrans alpha x ≫ stalkFunctorInvNatTrans alpha x = 𝟙 _ := sorry

/-- The named inverse associated-sheaf stalk transformation followed by the comparison is the
identity. -/
@[simp, stacks 01BH "associated-sheaf stalk natural inverse-forward law"]
theorem stalkFunctorNatTrans_inv_hom_id
    (alpha : R →+* X.globalSectionsRing) (x : X) :
    stalkFunctorInvNatTrans alpha x ≫ stalkFunctorNatTrans alpha x = 𝟙 _ := sorry

/-- Lemma 17.10.5 (5) (01BH): extension of scalars from global sections to the stalk is naturally
isomorphic to taking the stalk of the associated module sheaf. -/
@[stacks 01BH "(5)"]
noncomputable def stalkFunctorIso
    (alpha : R →+* X.globalSectionsRing) (x : X) :
    stalkExtensionFunctor alpha x ≅ stalkFunctor alpha x where
  hom := stalkFunctorNatTrans alpha x
  inv := stalkFunctorInvNatTrans alpha x
  hom_inv_id := stalkFunctorNatTrans_hom_inv_id alpha x
  inv_hom_id := stalkFunctorNatTrans_inv_hom_id alpha x

/-- A component of `stalkFunctorIso` is the literal associated-sheaf stalk comparison
isomorphism. -/
@[simp, stacks 01BH "associated-sheaf stalk natural isomorphism component"]
theorem stalkFunctorIso_app
    (alpha : R →+* X.globalSectionsRing) (x : X) (M : ModuleCat.{u} R) :
    (stalkFunctorIso alpha x).app M = stalkComparisonIso alpha M x := sorry

/-- The forward natural transformation of `stalkFunctorIso` is the comparison family. -/
@[simp, stacks 01BH "associated-sheaf stalk natural isomorphism hom"]
theorem stalkFunctorIso_hom
    (alpha : R →+* X.globalSectionsRing) (x : X) :
    (stalkFunctorIso alpha x).hom = stalkFunctorNatTrans alpha x := sorry

/-- The inverse natural transformation of `stalkFunctorIso` is the named inverse family. -/
@[simp, stacks 01BH "associated-sheaf stalk natural isomorphism inverse"]
theorem stalkFunctorIso_inv
    (alpha : R →+* X.globalSectionsRing) (x : X) :
    (stalkFunctorIso alpha x).inv = stalkFunctorInvNatTrans alpha x := sorry

/-- A forward component of `stalkFunctorIso` is the canonical associated-sheaf stalk
comparison. -/
@[simp, stacks 01BH "associated-sheaf stalk natural isomorphism hom component"]
theorem stalkFunctorIso_hom_app
    (alpha : R →+* X.globalSectionsRing) (x : X) (M : ModuleCat.{u} R) :
    (stalkFunctorIso alpha x).hom.app M = stalkComparison alpha M x := sorry

/-- An inverse component of `stalkFunctorIso` is the named associated-sheaf stalk comparison
inverse. -/
@[simp, stacks 01BH "associated-sheaf stalk natural isomorphism inverse component"]
theorem stalkFunctorIso_inv_app
    (alpha : R →+* X.globalSectionsRing) (x : X) (M : ModuleCat.{u} R) :
    (stalkFunctorIso alpha x).inv.app M = stalkComparisonInv alpha M x := sorry

/-- The objectwise associated-sheaf stalk formula. -/
@[stacks 01BH "stalk formula"]
noncomputable abbrev stalkIso
    (alpha : R →+* X.globalSectionsRing) (M : ModuleCat.{u} R) (x : X) :
    (ModuleCat.extendScalars (X.globalSectionsToStalk alpha x)).obj M ≅
      X.stalkModuleCat (obj alpha M) x :=
  (stalkFunctorIso alpha x).app M

end AlgebraicGeometry.RingedSpace.Module.Associated
