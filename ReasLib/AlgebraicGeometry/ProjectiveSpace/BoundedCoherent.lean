module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Ext
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.FlatPullbackSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Tensor
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.GradedObject.Duality

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Scheme.Hom
open DerivedCategory.TStructure
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- For a quasicoherent derived object on standard projective space over a field,
bounded coherent cohomology is equivalent to finite total dimension of derived global
sections after tensoring with every perfect object, of derived Ext from every perfect
object, and of derived global sections of the twists of degrees zero through the dimension. -/
theorem boundedCoherent_tfae
    (k : Type u) [Field k] (n : ℕ)
    (K : Scheme.DerivedQCoh (scheme k n)) :
    List.TFAE [
      DerivedCategory.cohomologyIn
          (SheafOfModules.isCoherent (scheme k n).toRingedSpace.ringCatSheaf) K.obj ∧
        (t.bounded : ObjectProperty
          (RingedSpace.ModuleDerived (scheme k n).toRingedSpace)) K.obj,
      ∀ E : RingedSpace.ModuleDerived (scheme k n).toRingedSpace,
        RingedSpace.ModuleDerived.IsPerfect E →
          GradedObject.FiniteTotalDimension
            (fun i : ℤ ↦
              (DerivedCategory.homologyFunctor (ModuleCat k) i).obj
                ((Scheme.FlatPullbackSections.baseSections (toSpec k n)).obj
                  (E ⊗ᴸ K.obj))),
      ∀ E : RingedSpace.ModuleDerived (scheme k n).toRingedSpace,
        RingedSpace.ModuleDerived.IsPerfect E →
          GradedObject.FiniteTotalDimension
            (fun i : ℤ ↦
              DerivedExt.value (toSpec k n) E K.obj i),
      ∀ d : Fin (n + 1),
        GradedObject.FiniteTotalDimension
          (fun i : ℤ ↦
            (DerivedCategory.homologyFunctor (ModuleCat k) i).obj
              ((Scheme.FlatPullbackSections.baseSections (toSpec k n)).obj
                (K.obj ⊗ᴸ (DerivedCategory.singleFunctor (scheme k n).Modules 0).obj
                  (twistingSheaf k n (d : ℤ)))))
    ] := sorry

end AlgebraicGeometry.ProjectiveSpace

end
