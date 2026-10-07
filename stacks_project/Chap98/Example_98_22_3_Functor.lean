module

public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap98.Example_98_22_3_BaseChange

/-!
# The global-sections functor and its associated category fibred in groupoids

The source functor sends `T/S` to the global sections `Γ(W_T, F_T)`. The associated
category fibred in groupoids over `Over (S Λ)` is the discrete Grothendieck construction of
that set-valued presheaf, forgotten from sets to groupoids.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TypeCat
open AlgebraicGeometry
open FiberedCategoryOver
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.GlobalSections

variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable {W : Scheme.{u}} (w : W ⟶ S Λ)
variable (F : W.Modules)

/-- The set-valued functor `T/S ↦ Γ(W_T, F_T)` on `(Sch/S)^{op}`. -/
def sectionsFunctor : (Over (S Λ))ᵒᵖ ⥤ Type u where
  obj T := (Γ(modulePullback w F T.unop, ⊤) : Type u)
  map {T T'} f := TypeCat.ofHom (sectionsRestrict w F f.unop)
  map_id := sorry
  map_comp := sorry

/-- Evaluating `sectionsFunctor` on `T` recovers the global sections of `F_T`. -/
theorem sectionsFunctor_obj (T : (Over (S Λ))ᵒᵖ) :
    (sectionsFunctor w F).obj T = Γ(modulePullback w F T.unop, ⊤) :=
  sorry

/-- `sectionsFunctor` acts on morphisms by restriction of global sections along base change. -/
theorem sectionsFunctor_map {T T' : (Over (S Λ))ᵒᵖ} (f : T ⟶ T') :
    (sectionsFunctor w F).map f = TypeCat.ofHom (sectionsRestrict w F f.unop) :=
  sorry

/-- The category fibred in groupoids associated to the global-sections functor. -/
def toGroupoids : GroupoidsOver (S Λ) :=
  (Sets.toGroupoids (Over (S Λ))).obj ((Sets.ofPresheaf (Over (S Λ))).obj (sectionsFunctor w F))

/-- The groupoid fibration of the global-sections functor is the discrete Grothendieck
construction of `sectionsFunctor`, forgotten to groupoids. -/
theorem toGroupoids_spec :
    toGroupoids w F =
      (Sets.toGroupoids (Over (S Λ))).obj
        ((Sets.ofPresheaf (Over (S Λ))).obj (sectionsFunctor w F)) :=
  sorry

/-- The projection of `toGroupoids` is the opposite category-of-elements projection of
`sectionsFunctor`. -/
theorem toGroupoids_p :
    (toGroupoids w F).p = ((Sets.ofPresheaf (Over (S Λ))).obj (sectionsFunctor w F)).p :=
  sorry

end AlgebraicGeometry.GroupoidsOver.GlobalSections
