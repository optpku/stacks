module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushforward.Shift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.RestrictedPushforward
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Adjunction
public import Mathlib.CategoryTheory.Shift.Adjunction

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory ComplexShape ObjectProperty
open CategoryTheory.Pretriangulated

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}}

/-- Restricted derived pullback is left adjoint to restricted derived pushforward on complexes
with quasi-coherent cohomology. -/
noncomputable def pullbackPushforwardCohomologyAdjunction {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    pullback f ⊣ pushforwardCohomologyIn f :=
  ObjectProperty.FullSubcategory.adjunction
    (ModuleDerived.pullback f) (Modules.moduleDerivedPushforward f)
    (ModuleDerived.pullbackPushforwardAdjunction f)
    (ModuleDerived.pullback_preservesQuasiCoherent f) (pushforwardCohomologyIn.mapsTo f)

/-- Restricted derived pushforward carries the ambient canonical shift. -/
noncomputable instance pushforwardCohomologyIn.commShift
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    (pushforwardCohomologyIn f).CommShift ℤ :=
  inferInstanceAs (((derivedQuasiCoherentModuleProperty Y).lift
    (inclusion X ⋙ Modules.moduleDerivedPushforward f)
    (fun E ↦ pushforwardCohomologyIn.mapsTo f E.obj E.property)).CommShift ℤ)

/-- The shift of a specified right adjoint induced by its adjunction to derived pushforward. -/
@[implicit_reducible]
noncomputable def rightAdjointCommShift
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a) :
    a.CommShift ℤ :=
  aAdjunction.rightAdjointCommShift ℤ

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
