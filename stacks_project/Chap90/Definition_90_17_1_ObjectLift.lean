module

public import ReasLib.CategoryTheory.Fibered.Lifts

/-! Compatibility checks for the shared category of lifts API. -/

/- The promoted API remains available through the historical item import. -/
#check CategoryTheory.Functor.ObjectLift
#check CategoryTheory.Functor.ObjectLift.domain
#check CategoryTheory.Functor.ObjectLift.ofHom
#check CategoryTheory.Functor.ObjectLift.forget
#check CategoryTheory.Functor.lifts
#check CategoryTheory.Functor.lifts_mk
