/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Completion
public import ReasLib.Algebra.Module.IdealPower.Quotient

@[expose] public section

open CategoryTheory CategoryTheory.Limits DerivedCategory
open CategoryTheory.DerivedCategory.LocalCohomology

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.LocalCohomology.Completion

variable {A : Type u} [CommRing A]

/-- The map from local cohomology of a module to the local cohomology of its
positive ideal-power quotient at a fixed stage. -/
noncomputable def cohomologyQuotientMap (I J : Ideal A)
    (RΓ : DerivedCategory (ModuleCat.{u} A) ⥤ IdealPowerTorsion J)
    (M : ModuleCat.{u} A) (i : ℤ) (n : ℕ) :
    (homologyFunctor (ModuleCat.{u} A) i).obj
        (RΓ.obj (ModuleCat.single0 M)).obj ⟶
      (homologyFunctor (ModuleCat.{u} A) i).obj
        ((quotientSystem I J RΓ M).obj (Opposite.op n)) :=
  (homologyFunctor (ModuleCat.{u} A) i).map
    ((RΓ.map
      (ModuleCat.single0Functor.map
        (ModuleCat.ofHom
          (Submodule.mkQ
            ((I ^ (n + 1)) • (⊤ : Submodule A (M : Type u)))) ≫
          eqToHom
            (rfl : ModuleCat.of A
                ((M : Type u) ⧸
                  ((I ^ (n + 1)) • (⊤ : Submodule A (M : Type u)))) =
              Ideal.PowerQuotient.positiveStage I M n)))).hom) ≫
    eqToHom
      (congrArg (fun K ↦ (homologyFunctor (ModuleCat.{u} A) i).obj K)
        (quotientSystem_obj I J RΓ M n).symm)

/-- The quotient-induced maps form a cone over the positive local-cohomology
tower. -/
theorem cohomologyQuotientMap_naturality (I J : Ideal A)
    (RΓ : DerivedCategory (ModuleCat.{u} A) ⥤ IdealPowerTorsion J)
    (M : ModuleCat.{u} A) (i : ℤ) {m n : ℕᵒᵖ} (f : m ⟶ n) :
    ((Functor.const ℕᵒᵖ).obj
        ((homologyFunctor (ModuleCat.{u} A) i).obj
          (RΓ.obj (ModuleCat.single0 M)).obj)).map f ≫
        cohomologyQuotientMap I J RΓ M i n.unop =
      cohomologyQuotientMap I J RΓ M i m.unop ≫
        (quotientSystem I J RΓ M ⋙
          homologyFunctor (ModuleCat.{u} A) i).map f := sorry

/-- The explicit cone whose legs are induced by the quotient projections. -/
noncomputable def cohomologyQuotientCone (I J : Ideal A)
    (RΓ : DerivedCategory (ModuleCat.{u} A) ⥤ IdealPowerTorsion J)
    (M : ModuleCat.{u} A) (i : ℤ) :
    Cone (quotientSystem I J RΓ M ⋙ homologyFunctor (ModuleCat.{u} A) i) :=
  { pt := (homologyFunctor (ModuleCat.{u} A) i).obj
        (RΓ.obj (ModuleCat.single0 M)).obj
    π :=
      { app := fun n ↦ cohomologyQuotientMap I J RΓ M i n.unop
        naturality := fun m n f ↦ cohomologyQuotientMap_naturality I J RΓ M i f } }

/-- The canonical comparison from local cohomology to the inverse limit of
the positive ideal-power quotient tower. -/
noncomputable def cohomologyToLimit (I J : Ideal A)
    (RΓ : DerivedCategory (ModuleCat.{u} A) ⥤ IdealPowerTorsion J)
    (M : ModuleCat.{u} A) (i : ℤ) :
    (homologyFunctor (ModuleCat.{u} A) i).obj
        (RΓ.obj (ModuleCat.single0 M)).obj ⟶
      limit (quotientSystem I J RΓ M ⋙ homologyFunctor (ModuleCat.{u} A) i) :=
  limit.lift (quotientSystem I J RΓ M ⋙ homologyFunctor (ModuleCat.{u} A) i)
    (cohomologyQuotientCone I J RΓ M i)

/-- The canonical comparison has the quotient-induced map as each of its
projections. -/
theorem cohomologyToLimit_π (I J : Ideal A)
    (RΓ : DerivedCategory (ModuleCat.{u} A) ⥤ IdealPowerTorsion J)
    (M : ModuleCat.{u} A) (i : ℤ) (n : ℕ) :
    cohomologyToLimit I J RΓ M i ≫
        limit.π (quotientSystem I J RΓ M ⋙
          homologyFunctor (ModuleCat.{u} A) i) (Opposite.op n) =
      cohomologyQuotientMap I J RΓ M i n := sorry

end CategoryTheory.DerivedCategory.LocalCohomology.Completion
