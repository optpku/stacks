module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Total
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.Algebra
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Underlying

/-!
# Total conormal algebras

The total conormal algebra is the quasi-coherent algebra obtained by summing all homogeneous
pieces of the conormal algebra of an immersion.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ConormalAlgebra

variable {X Z : Scheme.{u}}

/-- The module underlying the total conormal algebra of an immersion is quasi-coherent. -/
theorem total_isQuasicoherent (i : Z ⟶ X) [IsImmersion i] :
    ((restrictionAlong
        (@GradedAlgebraSheaf.totalAlgebra _ _ _ _ _ _ Z.sheaf (ConormalAlgebra i)
          (KernelIdeal.AssociatedGraded.algebra_isCommutative.{u, u}
            (RingedSpace.Hom.inverseImageStructureSheafHomComm i.toShHom))).hom).obj
      (unitModule (Opens.grothendieckTopology Z)
        (@GradedAlgebraSheaf.totalAlgebra _ _ _ _ _ _ Z.sheaf (ConormalAlgebra i)
          (KernelIdeal.AssociatedGraded.algebra_isCommutative.{u, u}
            (RingedSpace.Hom.inverseImageStructureSheafHomComm i.toShHom))).right)).IsQuasicoherent :=
  sorry

/-- The total conormal algebra of an immersion, as a quasi-coherent algebra over its source. -/
noncomputable def total (i : Z ⟶ X) [IsImmersion i] : Z.QcAlgebraUnder :=
  ⟨@GradedAlgebraSheaf.totalAlgebra _ _ _ _ _ _ Z.sheaf (ConormalAlgebra i)
      (KernelIdeal.AssociatedGraded.algebra_isCommutative.{u, u}
        (RingedSpace.Hom.inverseImageStructureSheafHomComm i.toShHom)),
    total_isQuasicoherent i⟩

/-- The module underlying the total conormal algebra is the coproduct of its homogeneous
conormal pieces. -/
noncomputable def totalUnderlyingModuleIso (i : Z ⟶ X) [IsImmersion i] :
    (CategoryTheory.GradedObject.Total.functor (I := ℕ) (C := Z.Modules)).obj
        (ConormalAlgebra i).toGradedObject ≅
      QcAlgebraUnder.underlyingModule Z (total i) :=
  @GradedAlgebraSheaf.totalUnderlyingModuleIso _ _ _ _ _ _ Z.sheaf (ConormalAlgebra i)
    (KernelIdeal.AssociatedGraded.algebra_isCommutative.{u, u}
      (RingedSpace.Hom.inverseImageStructureSheafHomComm i.toShHom))

end AlgebraicGeometry.Scheme.ConormalAlgebra
