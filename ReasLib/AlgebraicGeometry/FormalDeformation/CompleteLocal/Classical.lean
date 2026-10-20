module

public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Instances

/-!
# The classical complete local base algebra

When the base is complete local and its residue field is identified with `k`,
it is an initial object of the category of complete local algebras over it.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ArtinianLocalAlgCat

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

/-- The complete local base algebra with its canonical classical residue identification. -/
noncomputable def classical [IsClassical Λ k] : CompleteLocalAlgCat Λ k :=
  of Λ IsClassical.residueFieldIso

/-- The carrier of the classical complete local base algebra is the base ring. -/
theorem classical_carrier [IsClassical Λ k] :
    (classical : CompleteLocalAlgCat Λ k).carrier = Λ := rfl

/-- The structure map from a classical base to a complete local algebra is local. -/
instance instIsLocalHom_algebraMap_classical [IsClassical Λ k]
    (R : CompleteLocalAlgCat Λ k) : IsLocalHom (algebraMap Λ R.carrier) := sorry

/-- The structure map from the classical base respects the chosen residue identifications. -/
theorem fromClassical_residue_compat [IsClassical Λ k] (R : CompleteLocalAlgCat Λ k) :
    residueCompat (A := classical) (B := R) (Algebra.ofId Λ R.carrier)
        ⟨(instIsLocalHom_algebraMap_classical R).map_nonunit⟩ =
      residueIsoHom classical := sorry

/-- The structure morphism from the classical complete local base algebra. -/
noncomputable def fromClassical [IsClassical Λ k] (R : CompleteLocalAlgCat Λ k) :
    classical ⟶ R :=
  Hom.of (Algebra.ofId Λ R.carrier)
    ⟨(instIsLocalHom_algebraMap_classical R).map_nonunit⟩
    (fromClassical_residue_compat R)

/-- The underlying algebra homomorphism of the classical structure morphism is the structure map. -/
theorem fromClassical_hom [IsClassical Λ k] (R : CompleteLocalAlgCat Λ k) :
    (fromClassical R).hom = Algebra.ofId Λ R.carrier := rfl

/-- Every morphism from the classical complete local base algebra is its structure morphism. -/
theorem fromClassical_unique [IsClassical Λ k] {R : CompleteLocalAlgCat Λ k}
    (f : classical ⟶ R) : f = fromClassical R := sorry

/-- The classical complete local base algebra is initial, with its structure morphisms. -/
noncomputable def classicalIsInitial [IsClassical Λ k] :
    IsInitial (classical : CompleteLocalAlgCat Λ k) :=
  IsInitial.ofUniqueHom fromClassical
    (fun R morphism ↦ fromClassical_unique (R := R) morphism)

/-- The morphism supplied by initiality of the classical base is its structure morphism. -/
theorem classicalIsInitial_to [IsClassical Λ k] (R : CompleteLocalAlgCat Λ k) :
    IsInitial.to classicalIsInitial R = fromClassical R := sorry

/-- Complete local algebras over a classical base have an initial object. -/
instance instHasInitial_classical [IsClassical Λ k] :
    HasInitial (CompleteLocalAlgCat Λ k) := classicalIsInitial.hasInitial

end CompleteLocalAlgCat
