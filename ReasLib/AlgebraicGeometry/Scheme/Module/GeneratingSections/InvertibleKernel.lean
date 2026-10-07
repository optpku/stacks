module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Generated
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.CategoryTheory.Monoidal.Invertible

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- If a finite family of global sections generates an invertible module on a scheme, then
the tensor product of the kernel of its evaluation morphism with that module is globally
generated. -/
theorem kernelTensorSectionFamilyHom_isGloballyGenerated
    {X : Scheme.{u}} (L : X.Modules)
    [CategoryTheory.MonoidalCategory.isInvertibleObject L]
    (n : ℕ) (s : Fin (n + 1) → L.sections)
    (hgen : Epi
      (L.freeHomEquiv.symm (fun i : ULift.{u} (Fin (n + 1)) ↦ s i.down))) :
    SheafOfModules.IsGloballyGenerated
      (tensorObj
        (kernel (L.freeHomEquiv.symm
          (fun i : ULift.{u} (Fin (n + 1)) ↦ s i.down))) L : X.Modules) := sorry

end AlgebraicGeometry.Scheme.Modules
