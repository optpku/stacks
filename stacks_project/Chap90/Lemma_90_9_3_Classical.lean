/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import stacks_project.Chap90.Definition_90_3_1_Classical
public import stacks_project.Chap90.Definition_90_7_3_CompleteLocal

/-!
# The classical base object of `CompleteLocalAlgCat`

In the classical case, `Λ` itself is an object of `Ĉ_Λ`, and it is initial:
every `R : CompleteLocalAlgCat Λ k` has a unique structure morphism from this
base object.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open ArtinianLocalAlgCat

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

/-- `Λ` as an object of `CompleteLocalAlgCat Λ k` in the classical case, via the
classical residue identification `IsClassical.residueFieldIso`. -/
noncomputable def classical [IsClassical Λ k] : CompleteLocalAlgCat Λ k :=
  of Λ IsClassical.residueFieldIso

/-- The carrier of `classical` is `Λ`. -/
theorem classical_carrier [IsClassical Λ k] :
    (classical : CompleteLocalAlgCat Λ k).carrier = Λ := sorry

/-- The unique structure morphism `classical ⟶ R` in the classical case. -/
noncomputable def fromClassical [IsClassical Λ k] (R : CompleteLocalAlgCat Λ k) :
    classical ⟶ R where
  hom := Algebra.ofId Λ R.carrier
  isLocalHom := sorry
  residue_compat := sorry

/-- The underlying algebra map of `fromClassical R` is `Algebra.ofId Λ R.carrier`. -/
theorem fromClassical_hom [IsClassical Λ k] (R : CompleteLocalAlgCat Λ k) :
    (fromClassical R).hom = Algebra.ofId Λ R.carrier := sorry

/-- Any morphism `classical ⟶ R` equals `fromClassical R`. -/
theorem fromClassical_unique [IsClassical Λ k] {R : CompleteLocalAlgCat Λ k}
    (f : classical ⟶ R) : f = fromClassical R := sorry

/-- In the classical case, the structure map `Λ → R.carrier` is local. -/
instance instIsLocalHom_algebraMap_classical [IsClassical Λ k]
    (R : CompleteLocalAlgCat Λ k) : IsLocalHom (algebraMap Λ R.carrier) := sorry

/-- `classical` is an initial object of `CompleteLocalAlgCat Λ k`. -/
noncomputable def classicalIsInitial [IsClassical Λ k] :
    IsInitial (classical : CompleteLocalAlgCat Λ k) :=
  IsInitial.ofUniqueHom (fun R ↦ fromClassical R) sorry

/-- The unique morphism out of `classicalIsInitial` is `fromClassical`. -/
theorem classicalIsInitial_to [IsClassical Λ k] (R : CompleteLocalAlgCat Λ k) :
    IsInitial.to classicalIsInitial R = fromClassical R := sorry

/-- In the classical case, `CompleteLocalAlgCat Λ k` has an initial object. -/
instance instHasInitial_classical [IsClassical Λ k] :
    HasInitial (CompleteLocalAlgCat Λ k) := sorry

end CompleteLocalAlgCat
