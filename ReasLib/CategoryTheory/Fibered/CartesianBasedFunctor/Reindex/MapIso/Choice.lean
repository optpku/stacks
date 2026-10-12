/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Reindex.MapIso.Coherence
public import ReasLib.CategoryTheory.Fibered.Cleavage.ReindexIso.Choice

/-!
# Identity cartesian functors and change of cleavage

For the identity cartesian based functor, the general reindexing comparison is exactly the
canonical comparison between the two cleavages, with the orientation dictated by `mapIso`.
-/

@[expose] public section

universe uC vC uS vS

namespace CategoryTheory

open Functor

namespace CartesianBasedFunctor

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S] {p : S ⥤ C}

/-- For the identity cartesian based functor, `mapIso` is the reverse canonical
change-of-cleavage isomorphism. -/
@[simp]
theorem Reindex.mapIso.identityFunctor
    (chi₁ chi₂ : p.Cleavage) {U V : C} (f : V ⟶ U) (x : p.Fiber U) :
    Reindex.mapIso (CartesianBasedFunctor.id p) chi₁ chi₂ f x =
      (Functor.Cleavage.Reindex.uniqueIsoApp chi₁ chi₂ f x).symm := sorry

/-- The forward map of the identity-functor reindexing comparison is the inverse canonical
change-of-cleavage map. -/
@[simp]
theorem Reindex.mapIso.identityFunctor.hom
    (chi₁ chi₂ : p.Cleavage) {U V : C} (f : V ⟶ U) (x : p.Fiber U) :
    (Reindex.mapIso (CartesianBasedFunctor.id p) chi₁ chi₂ f x).hom =
      (Functor.Cleavage.Reindex.uniqueIsoApp chi₁ chi₂ f x).inv := sorry

/-- The inverse map of the identity-functor reindexing comparison is the forward canonical
change-of-cleavage map. -/
@[simp]
theorem Reindex.mapIso.identityFunctor.inv
    (chi₁ chi₂ : p.Cleavage) {U V : C} (f : V ⟶ U) (x : p.Fiber U) :
    (Reindex.mapIso (CartesianBasedFunctor.id p) chi₁ chi₂ f x).inv =
      (Functor.Cleavage.Reindex.uniqueIsoApp chi₁ chi₂ f x).hom := sorry

end CartesianBasedFunctor

end CategoryTheory
