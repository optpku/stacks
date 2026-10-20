/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.Complement
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian

/-!
# Factorization through a monomorphism from the open complement and completion

A morphism from a locally Noetherian algebraic space factors through a locally
finite-type monomorphism whenever it factors through it on the open complement
of a closed subset and on the completion along that subset.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.completionAlong

/-- A morphism from a locally Noetherian algebraic space factors through a
locally finite-type monomorphism if its restrictions to the open complement
of a closed subset and to the completion along that subset both factor
through the monomorphism. -/
@[stacks 0AR6]
theorem exists_factorThrough {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    [IsLocallyNoetherian X] (T : Closeds (Points X)) (f : X ⟶ Y) (g : Z ⟶ Y)
    [Mono g] [LocallyOfFiniteType g]
    (h_open : ∃ h : openComplementAlong X T ⟶ Z, h ≫ g = openComplementι X T ≫ f)
    (h_completion : ∃ h : completionAlong X T ⟶ Z.functorOfPoints,
      h ≫ g = ι X T ≫ f) :
    ∃ h : X ⟶ Z, h ≫ g = f :=
  sorry

/-- A morphism from a locally Noetherian algebraic space factors uniquely
through a locally finite-type monomorphism if its restrictions to the open
complement of a closed subset and to the completion along that subset both
factor through the monomorphism. -/
theorem existsUnique_factorThrough {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    [IsLocallyNoetherian X] (T : Closeds (Points X)) (f : X ⟶ Y) (g : Z ⟶ Y)
    [Mono g] [LocallyOfFiniteType g]
    (h_open : ∃ h : openComplementAlong X T ⟶ Z, h ≫ g = openComplementι X T ≫ f)
    (h_completion : ∃ h : completionAlong X T ⟶ Z.functorOfPoints,
      h ≫ g = ι X T ≫ f) :
    ∃! h : X ⟶ Z, h ≫ g = f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.completionAlong
