/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.EssentialImage
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.KernelAnnihilation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.ClosedImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.ClosedImmersion

/-!
# Quasi-coherent modules along closed immersions

Pushforward of quasi-coherent modules along a closed immersion of algebraic
spaces is exact and fully faithful, with essential image the modules annihilated
by the defining ideal sheaf. It also admits a right adjoint.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QCoh

variable {S : Scheme.{u}} {X Z : AlgebraicSpace S}

/-- Pushforward of quasi-coherent modules along a closed immersion of algebraic
spaces admits a right adjoint. -/
@[instance]
theorem pushforward_isLeftAdjoint (i : Z ⟶ X) [IsClosedImmersion i] :
    (pushforward i).IsLeftAdjoint := sorry

/-- Pushforward of quasi-coherent modules along a closed immersion of algebraic
spaces is exact. -/
theorem pushforwardExact (i : Z ⟶ X) [IsClosedImmersion i] :
    exactFunctor (QCoh Z) (QCoh X) (pushforward i) :=
  sorry

namespace pushforward

/-- Pushforward of quasi-coherent modules along a closed immersion of algebraic
spaces is full. -/
@[instance]
theorem full (i : Z ⟶ X) [IsClosedImmersion i] : (pushforward i).Full :=
  sorry

/-- Pushforward of quasi-coherent modules along a closed immersion of algebraic
spaces is faithful. -/
@[instance]
theorem faithful (i : Z ⟶ X) [IsClosedImmersion i] : (pushforward i).Faithful :=
  sorry

end pushforward

/-- A quasi-coherent module lies in the essential image of pushforward along a
closed immersion of algebraic spaces if and only if the kernel of the structure
sheaf map annihilates it. -/
theorem mem_essImage_iff_isAnnihilatedByKernel (i : Z ⟶ X) [IsClosedImmersion i]
    (H : QCoh X) :
    (pushforward i).essImage H ↔
      SheafOfModules.IsAnnihilatedByKernel
        (SheafOfModules.ChangeOfRings.homOverId (structureSheafMap i)) H.obj :=
  sorry

/-- A quasi-coherent module lies in the essential image of closed-immersion
pushforward if and only if every local section of the defining ideal sheaf acts
by zero. -/
theorem mem_essImage_iff_idealSheaf_smul_eq_zero (i : Z ⟶ X)
    [IsClosedImmersion i] (H : QCoh X) :
    (pushforward i).essImage H ↔
      ∀ U : (smallEtaleSite X)ᵒᵖ,
        ∀ s : (Hom.idealSheaf i).val.obj U,
          ∀ m : H.obj.val.obj U,
            ((Hom.idealSheafι i).val.app U s) • m = 0 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.QCoh
