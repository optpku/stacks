module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Category
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.IdealStalk
public import ReasLib.RingTheory.AdicCompletion.CompleteModule

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/-- The inverse limit of the stalk stages of a coherent formal module on a Noetherian
scheme is adically complete for the stalk ideal induced by its ideal-sheaf data. -/
theorem stalkLimit_isAdicComplete_of_coherentFormalModule
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (F : CoherentFormalModules X I) (y : X) :
    IsAdicComplete (RingedSpace.idealSheafStalkIdeal I.toSubobject y)
      (limit (F.obj ⋙ (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).ι ⋙
        X.toRingedSpace.stalkModuleFunctor y) :
        ModuleCat (X.presheaf.stalk y)) := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
