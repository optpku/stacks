module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSubobject.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Hom

/-!
# Structure-module comparisons and inverse-image ideal properties

The structure-module maps are the canonical comparisons associated to pullback
and pushforward. Inverse-image ideals preserve quasi-coherence and finite type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The canonical comparison `f^* 𝒪_Y ⟶ 𝒪_X` of structure modules. -/
abbrev pullbackObjUnitToUnit {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    (pullback f).obj (SheafOfModules.unit (structureSheaf Y)) ⟶
      SheafOfModules.unit (structureSheaf X) :=
  IdealSubobject.pullbackUnit f

#check (AlgebraicGeometry.AlgebraicSpace.unitUnderlyingIso :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    (Sheaf.InternalModule.ToInternal.underlying (structureSheaf X)).obj
      (SheafOfModules.unit (structureSheaf X)) ≅
      RingedSite.Hom.underlyingStructureSheaf (ringedSite X))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.unitToPushforwardObjUnit :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    SheafOfModules.unit (structureSheaf Y) ⟶
      (pushforward f).obj (SheafOfModules.unit (structureSheaf X)))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.pullbackObjUnitToUnit :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    (pullback f).obj (SheafOfModules.unit (structureSheaf Y)) ⟶
      SheafOfModules.unit (structureSheaf X))

#check (AlgebraicGeometry.AlgebraicSpace.IdealSubobject.pullbackUnit_eq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    IdealSubobject.pullbackUnit f =
      ((pullbackPushforwardAdjunction f).homEquiv
          (SheafOfModules.unit (structureSheaf Y))
          (SheafOfModules.unit (structureSheaf X))).symm
        (IdealSubobject.unitToPushforward f))

#check (AlgebraicGeometry.AlgebraicSpace.IdealSubobject.pullback_isQuasicoherent :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (I : IdealSubobject Y) [(I : Y.Modules).IsQuasicoherent] (f : X ⟶ Y),
    (I.pullback f : X.Modules).IsQuasicoherent)

#check (AlgebraicGeometry.AlgebraicSpace.IdealSubobject.pullback_isFiniteType :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (I : IdealSubobject Y) [(I : Y.Modules).IsFiniteType] (f : X ⟶ Y),
    (I.pullback f : X.Modules).IsFiniteType)

end AlgebraicGeometry.AlgebraicSpace.Modules
