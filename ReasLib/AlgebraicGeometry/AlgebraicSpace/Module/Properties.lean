module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeRestriction
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SmallEtale.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- A small étale module is quasicoherent if its realization on every étale scheme chart
is a quasicoherent scheme module. -/
def IsQuasicoherent (F : Modules X) : Prop :=
  ∀ U : site X, SheafOfModules.IsQuasicoherent.{u} ((toScheme U).obj F)

/-- A small étale module is of finite type if its realization on every étale scheme chart
is of finite type. -/
def IsFiniteType (F : Modules X) : Prop :=
  ∀ U : site X, SheafOfModules.IsFiniteType.{u} ((toScheme U).obj F)

/-- A small étale module is of finite presentation if its realization on every étale scheme
chart is of finite presentation. -/
def IsFinitePresentation (F : Modules X) : Prop :=
  ∀ U : site X, SheafOfModules.IsFinitePresentation.{u} ((toScheme U).obj F)

/-- Quasicoherence of a small étale module is tested on every étale scheme chart. -/
theorem isQuasicoherent_iff (F : Modules X) :
    IsQuasicoherent F ↔
      ∀ U : site X, SheafOfModules.IsQuasicoherent.{u} ((toScheme U).obj F) := sorry

/-- Finite type of a small étale module is tested on every étale scheme chart. -/
theorem isFiniteType_iff (F : Modules X) :
    IsFiniteType F ↔
      ∀ U : site X, SheafOfModules.IsFiniteType.{u} ((toScheme U).obj F) := sorry

/-- Finite presentation of a small étale module is tested on every étale scheme chart. -/
theorem isFinitePresentation_iff (F : Modules X) :
    IsFinitePresentation F ↔
      ∀ U : site X, SheafOfModules.IsFinitePresentation.{u} ((toScheme U).obj F) := sorry

section SiteComparisons

variable [∀ U : site X, HasWeakSheafify ((topology X).over U) AddCommGrpCat.{u}]
  [∀ U : site X, ((topology X).over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Chartwise quasicoherence agrees with local presentations on the small étale site when
the slice sheafification interfaces are available. -/
theorem isQuasicoherent_iff_site (F : Modules X) :
    IsQuasicoherent F ↔ SheafOfModules.IsQuasicoherent F := sorry

/-- Chartwise finite type agrees with local finite generation on the small étale site when
the slice sheafification interfaces are available. -/
theorem isFiniteType_iff_site (F : Modules X) :
    IsFiniteType F ↔ SheafOfModules.IsFiniteType F := sorry

/-- Chartwise finite presentation agrees with local finite presentations on the small
étale site when the slice sheafification interfaces are available. -/
theorem isFinitePresentation_iff_site (F : Modules X) :
    IsFinitePresentation F ↔ SheafOfModules.IsFinitePresentation F := sorry

end SiteComparisons

end AlgebraicGeometry.AlgebraicSpace.SmallEtale.Modules
