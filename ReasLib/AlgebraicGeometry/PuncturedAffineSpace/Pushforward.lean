/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.Algebra.Module.Graded.Shift.NatInt
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated
public import ReasLib.AlgebraicGeometry.PuncturedAffineSpace.Projectivization

/-!
# Pushforward of modules along projectivization

Associated sheaves from the polynomial spectrum restrict to punctured affine space along the
coordinate-spectrum comparison, and their projectivization pushforwards decompose into twists.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedAffineSpace

variable (A : Type u) [CommRing A] (n : ℕ)

/-- The comparison of punctured affine `(n + 1)`-space with `Spec(A[T_0,...,T_n])`. -/
noncomputable def toCoordinateSpectrum :
    (puncturedOpen (projectiveIndex n) A).toScheme ⟶
      Spec (CommRingCat.of (coordinateRing (Fin (n + 1)) A)) :=
  (puncturedOpen (projectiveIndex n) A).ι ≫
    (coordinateModelIso (projectiveIndex n) A).hom ≫
      Spec.map (CommRingCat.ofHom
        ((MvPolynomial.renameEquiv A
            (Equiv.ulift : projectiveIndex n ≃ Fin (n + 1))).symm.toRingEquiv.toRingHom))

/-- The restriction of the affine associated sheaf of a module to punctured affine space. -/
noncomputable def tildeRestrict
    (M : Type u) [AddCommGroup M] [Module (coordinateRing (Fin (n + 1)) A) M] :
    (puncturedOpen (projectiveIndex n) A).toScheme.Modules :=
  (Scheme.Modules.pullback (toCoordinateSpectrum A n)).obj
    (tilde (ModuleCat.of (CommRingCat.of (coordinateRing (Fin (n + 1)) A)) M))

/-- The restricted associated sheaf is the pullback of the affine associated sheaf. -/
theorem tildeRestrict_def
    (M : Type u) [AddCommGroup M] [Module (coordinateRing (Fin (n + 1)) A) M] :
    tildeRestrict A n M =
      (Scheme.Modules.pullback (toCoordinateSpectrum A n)).obj
        (tilde (ModuleCat.of (CommRingCat.of (coordinateRing (Fin (n + 1)) A)) M)) := sorry

/-- The coordinate-spectrum comparison is the composite of the punctured-open inclusion, the
affine-space coordinate-model isomorphism, and the polynomial coordinate renaming. -/
theorem toCoordinateSpectrum_comp :
    toCoordinateSpectrum A n =
      (puncturedOpen (projectiveIndex n) A).ι ≫
        (coordinateModelIso (projectiveIndex n) A).hom ≫
          Spec.map (CommRingCat.ofHom
            ((MvPolynomial.renameEquiv A
                (Equiv.ulift : projectiveIndex n ≃ Fin (n + 1))).symm.toRingEquiv.toRingHom)) := sorry

/-- The pushforward of the structure sheaf along projectivization is the coproduct of all
integer twists of the projective-space structure sheaf. -/
theorem pushforward_unit_coproduct_twists (A : Type u) [CommRing A] (n : ℕ) :
    IsIsomorphic
      ((Scheme.Modules.pushforward (toProjectiveSpace A n)).obj
        (SheafOfModules.unit
            (puncturedOpen (projectiveIndex n) A).toScheme.ringCatSheaf :
          (puncturedOpen (projectiveIndex n) A).toScheme.Modules))
      (∐ fun d : ℤ ↦ ProjectiveSpace.twistingSheaf A n d) := sorry

/-- For an integer-graded module, the projectivization pushforward of its restricted associated
sheaf is the coproduct of the associated sheaves of all grading shifts. -/
theorem pushforward_tildeRestrict_coproduct_shifts
    (A : Type u) [CommRing A] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module A M]
    [Module (coordinateRing (Fin (n + 1)) A) M]
    (ℳ : ℤ → Submodule A M)
    [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (ProjectiveSpace.grading A n) ℳ] :
    IsIsomorphic
      ((Scheme.Modules.pushforward (toProjectiveSpace A n)).obj (tildeRestrict A n M))
      (∐ fun d : ℤ ↦
        Proj.AssociatedModule.sheaf (ProjectiveSpace.grading A n)
          (GradedModule.shiftGrading ℳ d)) := sorry

end AlgebraicGeometry.PuncturedAffineSpace
