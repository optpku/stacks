module

public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.RingTheory.HopkinsLevitzki
public import stacks_project.Chap90.Definition_90_7_3_ArtinianLocal
public import stacks_project.Chap90.Definition_90_7_3_CompleteLocal

/-!
# Prorepresentable functors on Artinian local algebras

A covariant `Type`-valued functor on `ArtinianLocalAlgCat` is prorepresentable when it is
isomorphic to the restriction of `coyoneda.obj (op R)` along the inclusion into
`CompleteLocalAlgCat`.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

/-- An Artinian local ring is complete for the maximal-adic topology. -/
instance instIsCompleteLocalRing_carrier (A : ArtinianLocalAlgCat Λ k) :
    IsCompleteLocalRing A.carrier where
  toIsAdicComplete := sorry

/-- View an Artinian local `Λ`-algebra as an object of the completed base category. -/
def toComplete (A : ArtinianLocalAlgCat Λ k) : CompleteLocalAlgCat Λ k :=
  CompleteLocalAlgCat.of A.carrier A.residueFieldIso

/-- The embedding into `CompleteLocalAlgCat` is the identity on underlying algebras. -/
theorem toComplete_carrier (A : ArtinianLocalAlgCat Λ k) :
    (toComplete A).carrier = A.carrier := sorry

/-- The embedding preserves the residue-field identification with `k`. -/
theorem toComplete_residueFieldIso (A : ArtinianLocalAlgCat Λ k) :
    (toComplete A).residueFieldIso = A.residueFieldIso := sorry

/-- The inclusion functor `ArtinianLocalAlgCat Λ k ⥤ CompleteLocalAlgCat Λ k`. -/
noncomputable def inclusion : ArtinianLocalAlgCat Λ k ⥤ CompleteLocalAlgCat Λ k where
  obj := toComplete
  map {A B} (f : Hom A B) :=
    { hom := f.hom
      isLocalHom := f.isLocalHom
      residue_compat := f.residue_compat }
  map_id := sorry
  map_comp := sorry

/-- The inclusion sends an Artinian object to its complete-local view. -/
theorem inclusion_obj (A : ArtinianLocalAlgCat Λ k) :
    inclusion.obj A = toComplete A := sorry

/-- The inclusion acts on morphisms by the same underlying algebra map. -/
theorem inclusion_map {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) :
    (inclusion.map f).hom = f.hom := sorry

end ArtinianLocalAlgCat

namespace CompleteLocalAlgCat

/-- Restriction of covariant `coyoneda.obj (op R)` to `ArtinianLocalAlgCat`. -/
noncomputable def restrictedCoyoneda (R : CompleteLocalAlgCat Λ k) :
    ArtinianLocalAlgCat Λ k ⥤ Type u :=
  ArtinianLocalAlgCat.inclusion ⋙ coyoneda.obj (op R)

/-- On objects, restricted coyoneda is `R ⟶ inclusion.obj A`. -/
theorem restrictedCoyoneda_obj (R : CompleteLocalAlgCat Λ k) (A : ArtinianLocalAlgCat Λ k) :
    (restrictedCoyoneda R).obj A = (R ⟶ ArtinianLocalAlgCat.inclusion.obj A) := sorry

/-- On morphisms, restricted coyoneda is postcomposition with the included map. -/
theorem restrictedCoyoneda_map (R : CompleteLocalAlgCat Λ k) {A B : ArtinianLocalAlgCat Λ k}
    (f : A ⟶ B) :
    (restrictedCoyoneda R).map f =
      (coyoneda.obj (op R)).map (ArtinianLocalAlgCat.inclusion.map f) := sorry

end CompleteLocalAlgCat

namespace CategoryTheory.Functor

/-- A functor `F : ArtinianLocalAlgCat Λ k ⥤ Type u` is prorepresentable if it is isomorphic
to `restrictedCoyoneda R` for some `R : CompleteLocalAlgCat Λ k`. -/
class IsProrepresentable (F : ArtinianLocalAlgCat Λ k ⥤ Type u) : Prop where
  has_prorepresentation :
    ∃ R : CompleteLocalAlgCat Λ k, Nonempty (CompleteLocalAlgCat.restrictedCoyoneda R ≅ F)

/-- The restriction of `coyoneda.obj (op R)` to `ArtinianLocalAlgCat` is prorepresentable. -/
instance instIsProrepresentableRestrictedCoyoneda (R : CompleteLocalAlgCat Λ k) :
    IsProrepresentable (CompleteLocalAlgCat.restrictedCoyoneda R) := sorry

/-- Prorepresentability means existence of `R : CompleteLocalAlgCat Λ k` and a functor
isomorphism with `restrictedCoyoneda R`. -/
theorem isProrepresentable_iff (F : ArtinianLocalAlgCat Λ k ⥤ Type u) :
    IsProrepresentable F ↔
      ∃ R : CompleteLocalAlgCat Λ k, Nonempty (CompleteLocalAlgCat.restrictedCoyoneda R ≅ F) :=
  sorry

/-- Prorepresentability is invariant under isomorphism of functors. -/
theorem isProrepresentable_of_iso {F G : ArtinianLocalAlgCat Λ k ⥤ Type u} (e : F ≅ G)
    [IsProrepresentable F] : IsProrepresentable G := sorry

end CategoryTheory.Functor

