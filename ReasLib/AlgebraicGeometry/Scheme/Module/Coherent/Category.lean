/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Subquotient
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FiniteTypeGeneration
public import ReasLib.CategoryTheory.ObjectProperty.Cover

/-!
# The Category of Coherent Quasicoherent Modules

Coherent quasicoherent modules on a scheme form an object property. On a locally Noetherian
scheme this property is a Serre class, and on a Noetherian scheme it admits epi lifts.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.QCoh

/-- The object property of coherent quasicoherent modules on a scheme. -/
abbrev isCoherent (X : Scheme.{u}) : ObjectProperty (Scheme.QCoh X) :=
  (SheafOfModules.isCoherent X.ringCatSheaf).inverseImage (Scheme.QCoh.inclusion X)

namespace isCoherent

/-- A quasicoherent module is in `isCoherent X` exactly when its underlying module sheaf is
coherent. -/
theorem mem_iff (X : Scheme.{u}) (F : Scheme.QCoh X) :
    isCoherent X F ↔ F.obj.IsCoherent := sorry

/-- On a locally Noetherian scheme, coherent quasicoherent modules form a Serre class. -/
instance isSerreClass (X : Scheme.{u}) [IsLocallyNoetherian X] :
    (isCoherent X).IsSerreClass := sorry

/-- On a Noetherian scheme, epimorphisms onto coherent quasicoherent modules admit coherent
subobjects that remain epimorphic. -/
instance hasEpiLift (X : Scheme.{u}) [IsNoetherian X] :
    (isCoherent X).HasEpiLift := sorry

end isCoherent

end AlgebraicGeometry.Scheme.QCoh
