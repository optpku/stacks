/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Regularity.Implications
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject.Quasicoherent

/-!
# Regular ideal subobjects of schemes

Regularity conditions on an ideal subobject imply finiteness and quasi-coherence of its
represented module sheaf.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.IdealSubobject

variable {X : Scheme.{u}}

/-- A quasi-regular ideal subobject of a scheme is represented by a finite-type module sheaf. -/
@[instance]
theorem isFiniteType_of_isQuasiRegular (I : Scheme.IdealSubobject X)
    [RingedSpace.IsQuasiRegularIdealSheaf I] : I.toModule.IsFiniteType := sorry

/-- A quasi-regular ideal subobject of a scheme is represented by a quasi-coherent module
sheaf. -/
@[instance]
theorem isQuasicoherent_of_isQuasiRegular (I : Scheme.IdealSubobject X)
    [RingedSpace.IsQuasiRegularIdealSheaf I] : I.toModule.IsQuasicoherent := sorry

/-- An `H₁`-regular ideal subobject of a scheme is represented by a finite-type module sheaf. -/
@[instance]
theorem isFiniteType_of_isH1Regular (I : Scheme.IdealSubobject X)
    [RingedSpace.IsH1RegularIdealSheaf I] : I.toModule.IsFiniteType := sorry

/-- An `H₁`-regular ideal subobject of a scheme is represented by a quasi-coherent module
sheaf. -/
@[instance]
theorem isQuasicoherent_of_isH1Regular (I : Scheme.IdealSubobject X)
    [RingedSpace.IsH1RegularIdealSheaf I] : I.toModule.IsQuasicoherent := sorry

/-- A Koszul-regular ideal subobject of a scheme is represented by a finite-type module sheaf. -/
@[instance]
theorem isFiniteType_of_isKoszulRegular (I : Scheme.IdealSubobject X)
    [RingedSpace.IsKoszulRegularIdealSheaf I] : I.toModule.IsFiniteType := sorry

/-- A Koszul-regular ideal subobject of a scheme is represented by a quasi-coherent module
sheaf. -/
@[instance]
theorem isQuasicoherent_of_isKoszulRegular (I : Scheme.IdealSubobject X)
    [RingedSpace.IsKoszulRegularIdealSheaf I] : I.toModule.IsQuasicoherent := sorry

/-- A regular ideal subobject of a scheme is represented by a finite-type module sheaf. -/
@[instance]
theorem isFiniteType_of_isRegular (I : Scheme.IdealSubobject X)
    [RingedSpace.IsRegularIdealSheaf I] : I.toModule.IsFiniteType := sorry

/-- A regular ideal subobject of a scheme is represented by a quasi-coherent module sheaf. -/
@[instance]
theorem isQuasicoherent_of_isRegular (I : Scheme.IdealSubobject X)
    [RingedSpace.IsRegularIdealSheaf I] : I.toModule.IsQuasicoherent := sorry

end AlgebraicGeometry.Scheme.IdealSubobject
