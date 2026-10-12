/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import ReasLib.CategoryTheory.Functor.ShiftRepresented
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Derived.Homology.Shift
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Regular

/-!
# Hypercohomology representability

This leaf records the canonical representability interface for a family of derived DG-module
valued functors.  The generic composition is owned by `Functor.ShiftRepresented`; this file fixes
the representing object to the image of the regular DG module.
-/

@[expose] public section

open CategoryTheory
open DifferentialGradedCategory
open scoped DifferentialGradedCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

-- Mathlib intentionally keeps this construction non-global because a global instance breaks
-- sheaf/free elaboration.  The represented shift sequence must match derived cohomology's choice.
attribute [local instance] Abelian.hasFiniteBiproducts

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedModule.Hypercohomology

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable (𝒜 : DGA(𝒪))
variable (H : ℤ → DerivedCategory 𝒜 ⥤ AddCommGrpCat.{max (u + 1) (v + 1)})

/-- The family-level comparison with the shifted regular-module representable functor. -/
noncomputable def functorIso
    (hshift : ∀ n : ℤ,
      H n ≅ (shiftFunctor (DerivedCategory 𝒜) n) ⋙ H 0)
    (hzero : H 0 ≅
      preadditiveCoyoneda.obj
        (Opposite.op ((DerivedCategory.Q 𝒜).obj 𝒜.regularModule)))
    (n : ℤ) :
    H n ≅
      (shiftFunctor (DerivedCategory 𝒜) n) ⋙
        preadditiveCoyoneda.obj
          (Opposite.op ((DerivedCategory.Q 𝒜).obj 𝒜.regularModule)) :=
  Functor.ShiftRepresented.iso H
    (fun n ↦ shiftFunctor (DerivedCategory 𝒜) n)
    (preadditiveCoyoneda.obj
      (Opposite.op ((DerivedCategory.Q 𝒜).obj 𝒜.regularModule)))
    hshift hzero n

/-- The objectwise comparison obtained by evaluating `functorIso`; the target stays bundled as the
`preadditiveCoyoneda` value, whose underlying carrier is the corresponding morphism group. -/
noncomputable def objIso
    (hshift : ∀ n : ℤ,
      H n ≅ (shiftFunctor (DerivedCategory 𝒜) n) ⋙ H 0)
    (hzero : H 0 ≅
      preadditiveCoyoneda.obj
        (Opposite.op ((DerivedCategory.Q 𝒜).obj 𝒜.regularModule)))
    (M : DerivedCategory 𝒜) (n : ℤ) :
    (H n).obj M ≅
      ((shiftFunctor (DerivedCategory 𝒜) n) ⋙
        preadditiveCoyoneda.obj
          (Opposite.op ((DerivedCategory.Q 𝒜).obj 𝒜.regularModule))).obj M :=
  (functorIso (𝒜 := 𝒜) (H := H) hshift hzero n).app M

/-- The forward component of `functorIso` after evaluation at a derived DG module. -/
theorem functorIso_hom_app
    (hshift : ∀ n : ℤ,
      H n ≅ (shiftFunctor (DerivedCategory 𝒜) n) ⋙ H 0)
    (hzero : H 0 ≅
      preadditiveCoyoneda.obj
        (Opposite.op ((DerivedCategory.Q 𝒜).obj 𝒜.regularModule)))
    (M : DerivedCategory 𝒜) (n : ℤ) :
    (functorIso (𝒜 := 𝒜) (H := H) hshift hzero n).hom.app M =
      (hshift n).hom.app M ≫
        (hzero.hom.app ((shiftFunctor (DerivedCategory 𝒜) n).obj M)) := sorry

/-- The inverse component of `functorIso` after evaluation at a derived DG module. -/
theorem functorIso_inv_app
    (hshift : ∀ n : ℤ,
      H n ≅ (shiftFunctor (DerivedCategory 𝒜) n) ⋙ H 0)
    (hzero : H 0 ≅
      preadditiveCoyoneda.obj
        (Opposite.op ((DerivedCategory.Q 𝒜).obj 𝒜.regularModule)))
    (M : DerivedCategory 𝒜) (n : ℤ) :
    (functorIso (𝒜 := 𝒜) (H := H) hshift hzero n).inv.app M =
      (hzero.inv.app ((shiftFunctor (DerivedCategory 𝒜) n).obj M)) ≫
        (hshift n).inv.app M := sorry

end

end SheafOfModules.RingedSite.DifferentialGradedModule.Hypercohomology
