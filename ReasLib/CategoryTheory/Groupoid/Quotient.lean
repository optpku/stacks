module

public import ReasLib.CategoryTheory.Groupoid.InFunctors
public import ReasLib.CategoryTheory.Cofibered.Grothendieck

/-!
# Quotient of a groupoid in functors

The quotient of a groupoid in functors is the Grothendieck realization of its
evaluation functor. Its canonical quotient morphism sends an element to the
corresponding pair and a base arrow to a transported identity morphism.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

noncomputable section

universe u v w

namespace CategoryTheory.GroupoidInFunctors

variable {C : Type u} [Category.{v} C]

/-- The Grothendieck projection of the fibre-groupoid functor of `G`. -/
abbrev quotientFunctor (G : GroupoidInFunctors.{u, v, w} C) :
    Grothendieck (G.toFunctor ⋙ Grpd.forgetToCat) ⥤ C :=
  Functor.groupoidCopresheafProjection G.toFunctor

/-- The Grothendieck projection of a groupoid in functors is cofibered in groupoids. -/
theorem quotientFunctor_op_inGroupoids (G : GroupoidInFunctors.{u, v, w} C) :
    Functor.IsFibered.InGroupoids (quotientFunctor G).op :=
  Functor.groupoidCopresheafProjection.op_inGroupoids G.toFunctor

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
    (quotient G).p = quotientFunctor G := sorry

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

/-- Transported identity morphisms send an identity arrow of the category of elements
to an identity arrow of the quotient. -/
private theorem quotientMorphismFunctor_map_id (G : GroupoidInFunctors.{u, v, w} C)
    (element : G.U.Elements) :
    Functor.ofGroupoidValued.mkHom G.toFunctor (𝟙 element : element ⟶ element).val
        (eqToHom (𝟙 element : element ⟶ element).property) =
      𝟙 (quotientObj G element.1 element.2) := sorry

/-- Transported identity morphisms preserve composition of category-of-elements arrows. -/
private theorem quotientMorphismFunctor_map_comp (G : GroupoidInFunctors.{u, v, w} C)
    {first middle last : G.U.Elements} (earlier : first ⟶ middle) (later : middle ⟶ last) :
    Functor.ofGroupoidValued.mkHom G.toFunctor (earlier ≫ later).val
        (eqToHom (earlier ≫ later).property) =
      Functor.ofGroupoidValued.mkHom G.toFunctor earlier.val (eqToHom earlier.property) ≫
        Functor.ofGroupoidValued.mkHom G.toFunctor later.val (eqToHom later.property) := sorry

/-- The underlying total functor of the quotient morphism `U ⟶ [U/R]`. -/
def quotientMorphismFunctor (G : GroupoidInFunctors.{u, v, w} C) :
    G.U.Elements ⥤ (quotient G).total where
  obj p := quotientObj G p.1 p.2
  map f := Functor.ofGroupoidValued.mkHom G.toFunctor f.val (eqToHom f.property)
  map_id := private quotientMorphismFunctor_map_id G
  map_comp := private quotientMorphismFunctor_map_comp G

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
