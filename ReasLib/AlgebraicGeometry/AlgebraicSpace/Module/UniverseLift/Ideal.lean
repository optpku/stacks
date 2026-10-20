module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.UniverseLift.Morphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSubobject

/-! # Universe lifting of ideal inclusions

An ideal subobject of the structure module determines an ideal subobject of the
structure module on the universe-lifted commutative ringed site.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The inclusion of a lifted ideal sheaf into the lifted structure module. -/
noncomputable def liftedIdealArrow (I : IdealSubobject X) :
    liftModule I.toModule ⟶
      unitModule (smallEtaleTopology X) (commStructureSheafLift X) :=
  liftModuleMap I.arrow ≫ (liftedUnitIso X).hom

/-- The lifted ideal inclusion is a monomorphism. -/
instance liftedIdealArrow_mono (I : IdealSubobject X) :
    Mono (liftedIdealArrow I) := sorry

/-- An ideal subobject of the structure module, transported to the
universe-lifted commutative structure module. -/
noncomputable def liftedIdealSubobject (I : IdealSubobject X) :
    Subobject (unitModule (smallEtaleTopology X) (commStructureSheafLift X)) :=
  Subobject.mk (liftedIdealArrow I)

end AlgebraicGeometry.AlgebraicSpace.Modules
