/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints

/-!
# Associated points of modules on locally Noetherian algebraic spaces

The associated locus of a module on a locally Noetherian algebraic space is its
weakly associated locus. For quasi-coherent modules it can be tested on étale scheme charts.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- On a locally Noetherian algebraic space, the associated points of an `𝒪_X`-module
are its weakly associated points. -/
def associatedPoints [IsLocallyNoetherian X] (F : X.Modules) : Set (Points X) :=
  F.weakAss

/-- On a locally Noetherian algebraic space, `Ass(F)` equals `WeakAss(F)`. -/
theorem associatedPoints_eq_weakAss [IsLocallyNoetherian X] (F : X.Modules) :
    associatedPoints F = F.weakAss :=
  rfl

/-- Membership in the associated locus is the étale-stalk weak-association condition. -/
theorem mem_associatedPoints_iff [IsLocallyNoetherian X] (F : X.Modules) (x : Points X) :
    x ∈ associatedPoints F ↔ etaleStalkWeakAss F x :=
  Iff.rfl

/-- For a quasi-coherent module on a locally Noetherian algebraic space, membership in
`Ass(F)` is equivalent to association on some étale scheme chart. -/
theorem mem_associatedPoints_iff_existsEtaleAss [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsQuasicoherent] (x : Points X) :
    x ∈ associatedPoints F ↔ existsEtaleAss F x :=
  (mem_weakAss_iff_existsEtaleWeakAss F x).trans
    (existsEtaleAss_iff_existsEtaleWeakAss F x).symm

end AlgebraicGeometry.AlgebraicSpace.Modules
