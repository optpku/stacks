module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AdicLimit
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections
public import ReasLib.CategoryTheory.InverseSystem.Milnor.Derived.Canonical
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Definition
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open SheafOfModules.RingedSite.IdealSheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.AdicLimit

variable {X : Scheme.{u}} (I : X.IdealSheafData)
variable (F : SequentialInverseSystem X.Modules)

/-- The ordinary limit in degree zero is a homotopy limit of a quasi-coherent
ideal-adic quotient tower, with stage `n` corresponding to the quotient by `I ^ (n + 1)`. -/
@[stacks 0EI8]
theorem isOf [I.toModule.IsQuasicoherent]
    [∀ n : ℕ, (F.obj (op n)).IsQuasicoherent]
    [h_epi : ∀ n : ℕ, Epi (F.stepMap n)]
    (h_kernel : ∀ n : ℕ, kernelSubobject (F.stepMap n) =
      imageSubobject (powerAction I.toSubobject (F.obj (op (n + 1))) (n + 1))) :
    HomotopyLimit.IsOf
      (F ⋙ DerivedCategory.singleFunctor X.Modules (0 : ℤ))
      ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj (limit F)) := sorry

/-- The ordinary limit of a quasi-coherent ideal-adic quotient tower has zero positive
hypercohomology on every affine open. -/
@[stacks 0EI8]
theorem higherCohomologyIsZero [I.toModule.IsQuasicoherent]
    [∀ n : ℕ, (F.obj (op n)).IsQuasicoherent]
    [h_epi : ∀ n : ℕ, Epi (F.stepMap n)]
    (h_kernel : ∀ n : ℕ, kernelSubobject (F.stepMap n) =
      imageSubobject (powerAction I.toSubobject (F.obj (op (n + 1))) (n + 1)))
    (U : X.affineOpens) (p : ℕ) (hp : 0 < p) :
    IsZero (RingedSpace.moduleOpenHypercohomology X.toRingedSpace (U : X.Opens)
      ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj (limit F)) (p : ℤ)) := sorry

/-- In every integer degree `p`, global hypercohomology of the ordinary limit of a
quasi-coherent ideal-adic quotient tower lies in the Milnor short exact sequence, with the first
derived limit in degree `p - 1` and the ordinary limit in degree `p`. -/
@[stacks 0EI8]
theorem cohomologyShortExact [I.toModule.IsQuasicoherent]
    [∀ n : ℕ, (F.obj (op n)).IsQuasicoherent]
    [h_epi : ∀ n : ℕ, Epi (F.stepMap n)]
    (h_kernel : ∀ n : ℕ, kernelSubobject (F.stepMap n) =
      imageSubobject (powerAction I.toSubobject (F.obj (op (n + 1))) (n + 1))) (p : ℤ) :
    ∃ (ι :
        SequentialInverseSystem.Milnor.ProductCone.canonicalR1
            (((F ⋙ DerivedCategory.singleFunctor X.Modules (0 : ℤ)) ⋙
              RingedSpace.moduleDerivedSectionsAtOpenToAb X.toRingedSpace ⊤) ⋙
              DerivedCategory.homologyFunctor AddCommGrpCat.{u} (p - 1)) ⟶
          RingedSpace.moduleOpenHypercohomology X.toRingedSpace ⊤
            ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj (limit F)) p)
      (π :
        RingedSpace.moduleOpenHypercohomology X.toRingedSpace ⊤
            ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj (limit F)) p ⟶
          limit (((F ⋙ DerivedCategory.singleFunctor X.Modules (0 : ℤ)) ⋙
            RingedSpace.moduleDerivedSectionsAtOpenToAb X.toRingedSpace ⊤) ⋙
            DerivedCategory.homologyFunctor AddCommGrpCat.{u} p))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry

end AlgebraicGeometry.Scheme.Modules.AdicLimit

end
