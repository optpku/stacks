module

public import stacks_project.Chap90.Definition_90_21_1_Groupoid
public import stacks_project.Chap90.Remarks_90_5_2_Grothendieck

/-!
# Quotient of a groupoid in functors

The assignment `T ↦ (U(T), R(T), s, t, c)` is `GroupoidInFunctors.toFunctor`.
The quotient `[U/R]` is the associated category cofibered in groupoids, and
the quotient morphism `U ⟶ [U/R]` is the based functor sending `x ∈ U(T)` to
the Grothendieck object `(T, x)` and a base arrow `f` to `(f, id)`.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

noncomputable section

universe u v w

namespace CategoryTheory.GroupoidInFunctors

variable {C : Type u} [Category.{v} C]

/-- The quotient category cofibered in groupoids `[U/R]` associated to a groupoid
in functors on `C`. -/
def quotient (G : GroupoidInFunctors.{u, v, w} C) :
    CofiberedCategoryOver.Groupoids.{u, v, max u w, max v w} C :=
  Functor.ofGroupoidValued G.toFunctor

/-- The quotient `[U/R]` is the Grothendieck realization of the fibre-groupoid functor. -/
theorem quotient_eq (G : GroupoidInFunctors.{u, v, w} C) :
    quotient G = Functor.ofGroupoidValued G.toFunctor := sorry

/-- The projection of `[U/R]` is the Grothendieck forgetful functor of `G.toFunctor`. -/
theorem quotient_p (G : GroupoidInFunctors.{u, v, w} C) :
    (quotient G).p = Functor.groupoidCopresheafProjection G.toFunctor := sorry

/-- The total category of `[U/R]` is the Grothendieck construction of the fibre-groupoid
functor. -/
theorem quotient_total (G : GroupoidInFunctors.{u, v, w} C) :
    (quotient G).total = Grothendieck (G.toFunctor ⋙ Grpd.forgetToCat) := sorry

/-- The object `(T, x)` of `[U/R]` associated to an element `x ∈ U(T)`. -/
def quotientObj (G : GroupoidInFunctors.{u, v, w} C) (T : C) (x : G.U.obj T) :
    (quotient G).total :=
  Functor.ofGroupoidValued.mkObj G.toFunctor T x

/-- The object `(T, x)` of `[U/R]` lies over `T`. -/
theorem quotientObj_base (G : GroupoidInFunctors.{u, v, w} C) (T : C) (x : G.U.obj T) :
    (quotient G).p.obj (quotientObj G T x) = T := sorry

/-- The underlying total functor of the quotient morphism `U ⟶ [U/R]`. -/
def quotientMorphismFunctor (G : GroupoidInFunctors.{u, v, w} C) :
    G.U.Elements ⥤ (quotient G).total where
  obj p := quotientObj G p.1 p.2
  map f := Functor.ofGroupoidValued.mkHom G.toFunctor f.val (eqToHom f.property)
  map_id := sorry
  map_comp := sorry

/-- On objects, the total functor of the quotient morphism sends `⟨T, x⟩` to `(T, x)`. -/
theorem quotientMorphismFunctor_obj (G : GroupoidInFunctors.{u, v, w} C) (T : C)
    (x : G.U.obj T) :
    (quotientMorphismFunctor G).obj ⟨T, x⟩ = quotientObj G T x := sorry

/-- The base of the image of a category-of-elements arrow is the underlying arrow of `C`. -/
theorem quotientMorphismFunctor_map_base (G : GroupoidInFunctors.{u, v, w} C)
    {p q : G.U.Elements} (f : p ⟶ q) :
    ((quotientMorphismFunctor G).map f).base = f.val := sorry

/-- The Grothendieck fibre of the image of a category-of-elements arrow is the identity
of `U(f)(x)`, transported along the Elements witness. -/
theorem quotientMorphismFunctor_map_fiber (G : GroupoidInFunctors.{u, v, w} C)
    {p q : G.U.Elements} (f : p ⟶ q) :
    ((quotientMorphismFunctor G).map f).fiber =
      (eqToHom f.property :
        ((G.toFunctor ⋙ Grpd.forgetToCat).map f.val).toFunctor.obj p.2 ⟶ q.2) := sorry

/-- The total functor of the quotient morphism lies over `C`. -/
theorem quotientMorphismFunctor_comp_p (G : GroupoidInFunctors.{u, v, w} C) :
    quotientMorphismFunctor G ⋙ (quotient G).p = CategoryOfElements.π G.U := sorry

/-- The quotient morphism `U ⟶ [U/R]` of categories cofibered in groupoids over `C`. -/
def quotientMorphism (G : GroupoidInFunctors.{u, v, w} C) :
    (Functor.ofTypeValued G.U).toBasedCategory ⥤ᵇ (quotient G).toBasedCategory :=
  BasedFunctor.ofFunctor (quotientMorphismFunctor G) (quotientMorphismFunctor_comp_p G)

/-- On objects, the quotient morphism sends `x ∈ U(T)` to `(T, x)`. -/
theorem quotientMorphism_obj (G : GroupoidInFunctors.{u, v, w} C) (T : C)
    (x : G.U.obj T) :
    (quotientMorphism G).obj ⟨T, x⟩ = quotientObj G T x := sorry

/-- The quotient morphism is a morphism of categories over `C`. -/
theorem quotientMorphism_comp_p (G : GroupoidInFunctors.{u, v, w} C) :
    (quotientMorphism G).toFunctor ⋙ (quotient G).p = CategoryOfElements.π G.U := sorry

end CategoryTheory.GroupoidInFunctors
