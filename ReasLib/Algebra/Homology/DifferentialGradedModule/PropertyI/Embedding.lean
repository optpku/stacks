/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.HomologyMaps
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyI

/-!
# Two-step property I embeddings
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace DifferentialGradedModule.PropertyI

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, v} R)

/-- A two-step property I embedding records an admissible extension of two products of shifts of
`Aᵛ`, together with a map which is monic on the underlying graded module and on incoming
differential cokernels. -/
@[stacks 09KT "two-step property-I embeddings"]
structure Embedding (M : DifferentialGradedModule.{u, v} A) where
  /-- The admissible two-step presentation of the target. -/
  sequence : ShortComplex (DifferentialGradedModule.{u, v} A)
  /-- The presentation is admissibly short exact. -/
  admissible : DifferentialGradedModule.IsAdmissibleShortExact sequence
  /-- The chosen product-of-dual-shifts presentation of the left term. -/
  leftPiece : Piece A sequence.X₁
  /-- The chosen product-of-dual-shifts presentation of the right term. -/
  rightPiece : Piece A sequence.X₃
  /-- The embedding map into the middle term. -/
  ι : M ⟶ sequence.X₂
  /-- The embedding is monic after forgetting the differential. -/
  gradedMono : Mono ((forgetToGraded A).map ι)
  /-- The embedding is monic on incoming-differential cokernels in every degree. -/
  cokernelMono : Hom.MonoOnDifferentialCokernels ι

namespace Embedding

/-- The target module of a two-step property I embedding. -/
abbrev target {M : DifferentialGradedModule.{u, v} A} (E : Embedding A M) :=
  E.sequence.X₂

/-- The left term of a two-step property I embedding is a product of shifted dual regular
modules. -/
theorem left_mem {M : DifferentialGradedModule.{u, v} A} (E : Embedding A M) :
    IsProductOfShifts A E.sequence.X₁ := sorry

/-- The right term of a two-step property I embedding is a product of shifted dual regular
modules. -/
theorem right_mem {M : DifferentialGradedModule.{u, v} A} (E : Embedding A M) :
    IsProductOfShifts A E.sequence.X₃ := sorry

/-- A two-step property I embedding is monic in the category of right DG modules. -/
instance ιMono {M : DifferentialGradedModule.{u, v} A} (E : Embedding A M) : Mono E.ι := sorry

/-- The target of a two-step property I embedding has property I. -/
theorem target_hasPropertyI {M : DifferentialGradedModule.{u, v} A} (E : Embedding A M) :
    HasPropertyI A E.target := sorry

/-- Lemma 22.21.3 (09KT): every right DG `A`-module admits a two-step property I embedding which
is monic both on the underlying graded module and on incoming-differential cokernels. -/
@[stacks 09KT]
theorem nonempty (M : DifferentialGradedModule.{u, v} A) :
    Nonempty (Embedding A M) := sorry

end Embedding

end DifferentialGradedModule.PropertyI
