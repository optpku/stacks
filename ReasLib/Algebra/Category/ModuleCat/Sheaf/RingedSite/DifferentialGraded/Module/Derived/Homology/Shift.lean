/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Derived.Homology

/-!
# Shift sequence for DG derived cohomology

The degree-zero cohomology functor on the intrinsic DG derived category is equipped with a
shift sequence whose degree-`n` term is definitionally the degree-`n` cohomology functor.
The comparison is constructed by localization from the corresponding homotopy-category
comparison.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open DifferentialGradedCategory
open scoped DifferentialGradedCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

-- Mathlib intentionally keeps this construction non-global because a global instance breaks
-- sheaf/free elaboration.  The derived shift sequence must use the homotopy owner's choice.
attribute [local instance] Abelian.hasFiniteBiproducts

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedModule.DerivedCategory.Homology

section


variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- The shift comparison before descent to the DG derived category. -/
noncomputable def shiftSourceIso (𝒜 : DGA(𝒪))
    (n a a' : ℤ) (ha' : n + a = a') :
    Qh 𝒜 ⋙
        (shiftFunctor (DerivedCategory 𝒜) n ⋙ homologyFunctor 𝒜 a) ≅
      Qh 𝒜 ⋙ homologyFunctor 𝒜 a' :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((Qh 𝒜).commShiftIso n).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (shiftFunctor (K ℤ Mod(𝒜, d)) n)
      (factors 𝒜 a) ≪≫
    (Homotopy.homologyFunctor 𝒜 0).shiftIso n a a' ha' ≪≫
    (factors 𝒜 a').symm

/-- The canonical comparison between shifting derived cohomology and changing its degree. -/
noncomputable def shiftIso (𝒜 : DGA(𝒪))
    (n a a' : ℤ) (ha' : n + a = a') :
    shiftFunctor (DerivedCategory 𝒜) n ⋙ homologyFunctor 𝒜 a ≅
      homologyFunctor 𝒜 a' :=
  CategoryTheory.Localization.liftNatIso (Qh 𝒜) (Homotopy.quasiIso 𝒜)
    (Qh 𝒜 ⋙
      (shiftFunctor (DerivedCategory 𝒜) n ⋙ homologyFunctor 𝒜 a))
    (Qh 𝒜 ⋙ homologyFunctor 𝒜 a')
    (shiftFunctor (DerivedCategory 𝒜) n ⋙ homologyFunctor 𝒜 a)
    (homologyFunctor 𝒜 a') (shiftSourceIso 𝒜 n a a' ha')

/-- Degree-zero derived cohomology carries the shift sequence whose degree-`n` term is
degree-`n` derived cohomology. -/
noncomputable instance zeroShiftSequence (𝒜 : DGA(𝒪)) :
    (homologyFunctor 𝒜 0).ShiftSequence ℤ where
  sequence := homologyFunctor 𝒜
  isoZero := Iso.refl _
  shiftIso := shiftIso 𝒜
  shiftIso_zero := sorry
  shiftIso_add := sorry

/-- The degree-`n` term of the derived cohomology shift sequence is degree-`n` cohomology. -/
@[simp]
theorem shift (𝒜 : DGA(𝒪)) (n : ℤ) :
    (homologyFunctor 𝒜 0).shift n = homologyFunctor 𝒜 n := sorry

/-- The forward derived shift comparison is computed before localization on objects in the
image of `Qh`. -/
theorem shiftIso_hom_app_qh (𝒜 : DGA(𝒪))
    (n a a' : ℤ) (ha' : n + a = a') (X : K ℤ Mod(𝒜, d)) :
    (shiftIso 𝒜 n a a' ha').hom.app ((Qh 𝒜).obj X) =
      (shiftSourceIso 𝒜 n a a' ha').hom.app X := sorry

/-- The inverse derived shift comparison is computed before localization on objects in the
image of `Qh`. -/
theorem shiftIso_inv_app_qh (𝒜 : DGA(𝒪))
    (n a a' : ℤ) (ha' : n + a = a') (X : K ℤ Mod(𝒜, d)) :
    (shiftIso 𝒜 n a a' ha').inv.app ((Qh 𝒜).obj X) =
      (shiftSourceIso 𝒜 n a a' ha').inv.app X := sorry

/-- A derived cohomology shift map is the degree-`a` cohomology map followed by the canonical
shift comparison. -/
theorem shiftMap_eq (𝒜 : DGA(𝒪)) {X Y : DerivedCategory 𝒜}
    {n : ℤ} (f : X ⟶ Y⟦n⟧) (a a' : ℤ) (ha' : n + a = a') :
    (homologyFunctor 𝒜 0).shiftMap f a a' ha' =
      (homologyFunctor 𝒜 a).map f ≫
        (shiftIso 𝒜 n a a' ha').hom.app Y := sorry

end


end SheafOfModules.RingedSite.DifferentialGradedModule.DerivedCategory.Homology
