/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.HopkinsLevitzki
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

variable {Λ k}

/-- An Artinian local commutative ring is complete for its maximal-adic topology. -/
private abbrev completeLocalOfArtinian (ring : Type*) [CommRing ring] [IsLocalRing ring]
    [IsArtinianRing ring] : IsCompleteLocalRing ring := inferInstance

/-- An Artinian local ring is complete for the maximal-adic topology. -/
instance instIsCompleteLocalRing_carrier (A : ArtinianLocalAlgCat Λ k) :
    IsCompleteLocalRing A.carrier :=
  @completeLocalOfArtinian A.carrier A.carrier.commRing A.isLocalRing A.isArtinianRing

/-- View an Artinian local `Λ`-algebra as a complete local `Λ`-algebra. -/
noncomputable def toComplete (A : ArtinianLocalAlgCat Λ k) : CompleteLocalAlgCat Λ k :=
  @CompleteLocalAlgCat.of Λ k _ _ _ _ _ A.carrier A.carrier.commRing A.algebra
    (@instIsNoetherianRingOfIsArtinianRing A.carrier A.carrier.commRing.toRing A.isArtinianRing)
    (instIsCompleteLocalRing_carrier A)
    A.residueFieldIso

/-- The complete-local view has the same underlying ring as the Artinian object. -/
theorem toComplete_carrier (A : ArtinianLocalAlgCat Λ k) :
    (toComplete A).carrier = A.carrier := sorry

/-- The complete-local view has the same chosen residue-field identification. -/
theorem toComplete_residueFieldIso (A : ArtinianLocalAlgCat Λ k) :
    (toComplete A).residueFieldIso = A.residueFieldIso := sorry

/-- The morphism induced on complete local algebras by an Artinian local morphism. -/
noncomputable def toCompleteHom {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) :
    toComplete A ⟶ toComplete B :=
  CompleteLocalAlgCat.Hom.of f.hom f.isLocalHom f.residue_compat

/-- The identity law for the morphisms induced by the Artinian-to-complete inclusion. -/
theorem toCompleteHom_id (A : ArtinianLocalAlgCat Λ k) :
    toCompleteHom (𝟙 A) = 𝟙 (toComplete A) := sorry

/-- The composition law for the morphisms induced by the Artinian-to-complete inclusion. -/
theorem toCompleteHom_comp {A B C : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) (g : B ⟶ C) :
    toCompleteHom (f ≫ g) = toCompleteHom f ≫ toCompleteHom g := sorry

/-- The inclusion of Artinian local algebras into complete local algebras. -/
noncomputable def inclusion : ArtinianLocalAlgCat Λ k ⥤ CompleteLocalAlgCat Λ k where
  obj := toComplete
  map := toCompleteHom
  map_id := toCompleteHom_id
  map_comp := toCompleteHom_comp

/-- The inclusion sends an Artinian object to its complete-local view. -/
theorem inclusion_obj (A : ArtinianLocalAlgCat Λ k) :
    inclusion.obj A = toComplete A := sorry

/-- The inclusion preserves the underlying algebra homomorphism of each morphism. -/
theorem inclusion_map {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) :
    (inclusion.map f).hom = f.hom := sorry

end ArtinianLocalAlgCat
