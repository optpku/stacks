/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.DeltaFunctor.Cohomological
public import ReasLib.CategoryTheory.Pretriangulated.DeltaFunctor.Morphism
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Naturality of the Cohomological Delta-Functor Construction

A morphism of pretriangulated delta functors induces a morphism of the
cohomological delta functors obtained by postcomposing with a fixed
homological functor.
-/

open CategoryTheory.Pretriangulated

noncomputable section

universe vA vB vD uA uB uD

namespace CategoryTheory.DeltaFunctor.toCohomologicalDeltaFunctor

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]
variable {D : Type uD} [Category.{vD} D] [Limits.HasZeroObject D]
  [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable (H : D ⥤ B) [H.IsHomological] [H.ShiftSequence ℤ]

/-- A morphism of pretriangulated delta functors induces a morphism between
the associated cohomological delta functors. -/
@[stacks 05SR "naturality of the cohomological delta-functor construction"]
noncomputable def map {G G' : DeltaFunctor A D} (f : G ⟶ G')
    (hG : ∀ X : A, Limits.IsZero ((H.shift (-1)).obj (G.obj X)))
    (hG' : ∀ X : A, Limits.IsZero ((H.shift (-1)).obj (G'.obj X))) :
    CohomologicalDeltaFunctor.Hom (G.toCohomologicalDeltaFunctor H hG)
      (G'.toCohomologicalDeltaFunctor H hG') where
  app n := Functor.whiskerRight f.app (H.shift (n : ℤ))
  comm := sorry

/-- In degree `n`, the induced cohomological morphism is obtained by
postcomposing the underlying delta-functor morphism with shifted homology. -/
@[simp]
theorem map_app {G G' : DeltaFunctor A D} (f : G ⟶ G')
    (hG : ∀ X : A, Limits.IsZero ((H.shift (-1)).obj (G.obj X)))
    (hG' : ∀ X : A, Limits.IsZero ((H.shift (-1)).obj (G'.obj X)))
    (n : ℕ) :
    (map H f hG hG').app n =
      Functor.whiskerRight f.app (H.shift (n : ℤ)) := sorry

/-- The cohomological construction sends identity delta-functor morphisms to
identities. -/
@[simp]
theorem map_id (G : DeltaFunctor A D)
    (hG : ∀ X : A, Limits.IsZero ((H.shift (-1)).obj (G.obj X))) :
    map H (𝟙 G) hG hG =
      CohomologicalDeltaFunctor.Hom.id (G.toCohomologicalDeltaFunctor H hG) := sorry

/-- The cohomological construction preserves composition of delta-functor
morphisms. -/
@[simp]
theorem map_comp {G G' G'' : DeltaFunctor A D} (f : G ⟶ G')
    (g : G' ⟶ G'')
    (hG : ∀ X : A, Limits.IsZero ((H.shift (-1)).obj (G.obj X)))
    (hG' : ∀ X : A, Limits.IsZero ((H.shift (-1)).obj (G'.obj X)))
    (hG'' : ∀ X : A, Limits.IsZero ((H.shift (-1)).obj (G''.obj X))) :
    map H (f ≫ g) hG hG'' =
      CohomologicalDeltaFunctor.Hom.comp (map H f hG hG') (map H g hG' hG'') := sorry

/-- An isomorphism of pretriangulated delta functors induces an isomorphism
of the associated cohomological delta functors. -/
@[stacks 05SR "isomorphism of induced cohomological delta functors"]
noncomputable def mapIso {G G' : DeltaFunctor A D} (e : G ≅ G')
    (hG : ∀ X : A, Limits.IsZero ((H.shift (-1)).obj (G.obj X)))
    (hG' : ∀ X : A, Limits.IsZero ((H.shift (-1)).obj (G'.obj X))) :
    CohomologicalDeltaFunctor.HomIso (G.toCohomologicalDeltaFunctor H hG)
      (G'.toCohomologicalDeltaFunctor H hG') where
  hom := map H e.hom hG hG'
  inv := map H e.inv hG' hG
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward morphism of the induced cohomological isomorphism is `map`. -/
@[simp]
theorem mapIso_hom {G G' : DeltaFunctor A D} (e : G ≅ G')
    (hG : ∀ X : A, Limits.IsZero ((H.shift (-1)).obj (G.obj X)))
    (hG' : ∀ X : A, Limits.IsZero ((H.shift (-1)).obj (G'.obj X))) :
    (mapIso H e hG hG').hom = map H e.hom hG hG' := sorry

/-- The inverse morphism of the induced cohomological isomorphism is `map`. -/
@[simp]
theorem mapIso_inv {G G' : DeltaFunctor A D} (e : G ≅ G')
    (hG : ∀ X : A, Limits.IsZero ((H.shift (-1)).obj (G.obj X)))
    (hG' : ∀ X : A, Limits.IsZero ((H.shift (-1)).obj (G'.obj X))) :
    (mapIso H e hG hG').inv = map H e.inv hG' hG := sorry

end CategoryTheory.DeltaFunctor.toCohomologicalDeltaFunctor
