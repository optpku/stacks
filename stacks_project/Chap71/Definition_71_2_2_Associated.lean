/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap71.Definition_71_2_2_WeakAss

/-!
# Associated points of locally Noetherian algebraic spaces

On a locally Noetherian algebraic space, associated points of a module (resp. of
the space) are identified with weakly associated points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

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
  sorry

/-- Membership in `F.associatedPoints` is the weakly-associated-point predicate. -/
theorem mem_associatedPoints_iff [IsLocallyNoetherian X] (F : X.Modules) (x : Points X) :
    x ∈ associatedPoints F ↔ F.weaklyAssociatedAt x :=
  sorry

/-- For a quasi-coherent module on a locally Noetherian algebraic space, membership in
`Ass(F)` is equivalent to association on some étale scheme chart. -/
theorem mem_associatedPoints_iff_existsEtaleAss [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsQuasicoherent] (x : Points X) :
    x ∈ associatedPoints F ↔ existsEtaleAss F x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- On a locally Noetherian algebraic space, the associated points of `X` are its
weakly associated points. -/
def associatedPoints [IsLocallyNoetherian X] : Set (Points X) :=
  X.weakAss

/-- On a locally Noetherian algebraic space, the associated points of `X` equal
`WeakAss(X)`. -/
theorem associatedPoints_eq_weakAss [IsLocallyNoetherian X] :
    associatedPoints X = X.weakAss :=
  sorry

/-- Membership in the associated points of a locally Noetherian algebraic space is
weak association of the structure sheaf. -/
theorem mem_associatedPoints_iff [IsLocallyNoetherian X] (x : Points X) :
    x ∈ associatedPoints X ↔ x ∈ X.weakAss :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
