module

import ReasLib.AlgebraicGeometry.Scheme.Module.SectionsWithSupport
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/- Definition 28.24.6: `sectionsWithSupportIn T ℱ` is the subsheaf of sections of `ℱ`
supported on the closed subset `T`. -/
@[stacks 084L]
#check (AlgebraicGeometry.Scheme.Modules.sectionsWithSupportIn :
  ∀ {X : Scheme.{u}}, TopologicalSpace.Closeds X → X.Modules → X.Modules)

/- The supported-sections subsheaf has a canonical inclusion into the ambient module sheaf. -/
#check (AlgebraicGeometry.Scheme.Modules.sectionsWithSupportInι :
  ∀ {X : Scheme.{u}} (T : TopologicalSpace.Closeds X) (ℱ : X.Modules),
    AlgebraicGeometry.Scheme.Modules.sectionsWithSupportIn T ℱ ⟶ ℱ)

/- If the open complement of `T` is retrocompact and `ℱ` is quasicoherent, then the subsheaf of
sections supported on `T` is quasicoherent. -/
#check (AlgebraicGeometry.Scheme.Modules.sectionsWithSupportIn_isQuasicoherent :
  ∀ {X : Scheme.{u}} (T : TopologicalSpace.Closeds X),
    IsRetrocompact
        (SheafOfModules.ClosedSubset.SectionsWithSupport.openComplement T : Set X) →
      ∀ (ℱ : X.Modules) [ℱ.IsQuasicoherent],
        (AlgebraicGeometry.Scheme.Modules.sectionsWithSupportIn T ℱ).IsQuasicoherent)

end AlgebraicGeometry.Scheme.Modules
