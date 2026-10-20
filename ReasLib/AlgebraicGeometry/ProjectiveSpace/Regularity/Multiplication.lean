/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Regularity
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist.Multiplication

/-!
# Multiplication of sections of regular sheaves on projective space

This file relates Castelnuovo–Mumford regularity to multiplication by global sections of the
degree-one twisting sheaf.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- If a coherent sheaf on projective space over a field is `m`-regular, multiplication by
global sections of the degree-one twisting sheaf is surjective from degree `m` to degree
`m + 1`. -/
theorem twistOneGlobalSectionsTensorMap_surjective_of_isMRegular
    (k : Type u) [Field k] (n : ℕ) (ℱ : (scheme k n).Modules) [ℱ.IsCoherent]
    (m : ℤ) (hℱ : IsMRegular k n ℱ m) :
    Function.Surjective (twistOneGlobalSectionsTensorMap k n ℱ m) := sorry

end AlgebraicGeometry.ProjectiveSpace
