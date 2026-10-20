module

public import Mathlib.CategoryTheory.Limits.Final
public import ReasLib.Algebra.Category.Ring.KanExtension
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfSite
public import ReasLib.CategoryTheory.Sites.GlobalSections.ToposMorphism
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback on global-sections rings

This file constructs the canonical ring homomorphism
`GlobalSectionsRing Y ⟶ GlobalSectionsRing X` associated to a morphism `X ⟶ Y` of ringed
sites. Its underlying function is the structure-sheaf map on limits followed by native
initial reindexing along the opposite of the given representably flat base functor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe uX vX uY vY w

namespace RingedSite.Hom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [UnivLE.{uX, w}] [UnivLE.{uY, w}]
variable [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
variable [UnivLE.{max uY vX, w}]

/-- The underlying type of the global-sections ring is canonically the type of global sections
of the underlying structure sheaf. -/
noncomputable def globalSectionsUnderlyingIso (X : RingedSite.{uX, vX, w}) :
    (globalSectionsRing X : Type w) ≅
      (Sheaf.Γ X.siteTopology (Type w)).obj (underlyingStructureSheaf X) :=
  preservesLimitIso (forget RingCat.{w}) X.structureSheaf.obj ≪≫
    ((Sheaf.ΓNatIsoLim X.siteTopology (Type w)).app
      (underlyingStructureSheaf X)).symm

/-- The underlying function of pullback on global-sections rings. -/
noncomputable def globalSectionsMapToFun (f : X.Hom Y) :
    globalSectionsRing Y → globalSectionsRing X :=
  letI : RepresentablyFlat f.base := f.isMorphismOfSites.toRepresentablyFlat
  letI : f.base.Final := CategoryTheory.final_of_representablyFlat f.base
  (Limits.lim.map f.structureSheafMap.hom ≫
    (Functor.Initial.limitIso f.base.op X.structureSheaf.obj).hom).hom

/-- Pullback on global sections preserves zero. -/
theorem globalSectionsMapToFun_zero (f : X.Hom Y) :
    globalSectionsMapToFun f 0 = 0 := sorry

/-- Pullback on global sections preserves one. -/
theorem globalSectionsMapToFun_one (f : X.Hom Y) :
    globalSectionsMapToFun f 1 = 1 := sorry

/-- Pullback on global sections preserves addition. -/
theorem globalSectionsMapToFun_add (f : X.Hom Y) (a b : globalSectionsRing Y) :
    globalSectionsMapToFun f (a + b) =
      globalSectionsMapToFun f a + globalSectionsMapToFun f b := sorry

/-- Pullback on global sections preserves multiplication. -/
theorem globalSectionsMapToFun_mul (f : X.Hom Y) (a b : globalSectionsRing Y) :
    globalSectionsMapToFun f (a * b) =
      globalSectionsMapToFun f a * globalSectionsMapToFun f b := sorry

/-- Pullback along a morphism of ringed sites on global-sections rings. -/
@[stacks 0D6H "global-sections pullback"]
noncomputable def globalSectionsMap (f : X.Hom Y) :
    globalSectionsRing Y ⟶ globalSectionsRing X :=
  RingCat.ofHom
    { toFun := globalSectionsMapToFun (X := X) (Y := Y) f
      map_zero' := globalSectionsMapToFun_zero (X := X) (Y := Y) f
      map_one' := globalSectionsMapToFun_one (X := X) (Y := Y) f
      map_add' := globalSectionsMapToFun_add (X := X) (Y := Y) f
      map_mul' := globalSectionsMapToFun_mul (X := X) (Y := Y) f }

/-- Evaluating the global-sections ring map uses its canonical underlying function. -/
@[simp]
theorem globalSectionsMap_apply (f : X.Hom Y) (s : globalSectionsRing Y) :
    (globalSectionsMap f).hom s = globalSectionsMapToFun f s := sorry

/-- Restriction of scalars from `Γ(X, 𝒪_X)` to `Γ(Y, 𝒪_Y)` induced by a ringed-site morphism. -/
abbrev globalSectionsRestriction.{z₁, u₁, v₁, u₂, v₂, w₁}
    {X : RingedSite.{u₁, v₁, w₁}} {Y : RingedSite.{u₂, v₂, w₁}}
    [UnivLE.{u₁, w₁}] [UnivLE.{u₂, w₁}]
    [UnivLE.{max u₁ v₁, w₁}] [UnivLE.{max u₂ v₂, w₁}]
    [UnivLE.{max u₂ v₁, w₁}]
    (f : X.Hom Y) :
    _root_.ModuleCat.{z₁} (globalSectionsRing X) ⥤
      _root_.ModuleCat.{z₁} (globalSectionsRing Y) :=
  _root_.ModuleCat.restrictScalars.{z₁} (globalSectionsMap f).hom

end RingedSite.Hom

-- The function is assembled from canonical comparison maps.  Deferred obligations in this
-- declaration are confined to the ring-homomorphism laws and upstream naturality fields.
