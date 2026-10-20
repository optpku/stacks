module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Matching.FaceFamily.Cone
public import Mathlib.CategoryTheory.RepresentedBy
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Matching objects

The matching object is the limit of the canonical matching diagram. Keeping this limit as the
public owner gives downstream constructions projections and a representability API without
committing them to a tuple presentation of the matching families.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial SimplexCategory.Truncated

universe u v

namespace CategoryTheory.SimplicialObject.Truncated

variable {C : Type u} [Category.{v} C]

/-- `HasMatchingObjects C n` asserts existence of the next matching object for every
`n`-truncated simplicial object in `C`. This is weaker than requiring every limit of the
matching-index shape. -/
@[stacks 0189 "existence of matching objects"]
class HasMatchingObjects (C : Type u) [Category.{v} C] (n : ℕ) : Prop where
  /-- Every `n`-truncated simplicial object has its canonical matching limit. -/
  hasLimit (U : SimplicialObject.Truncated C n) : HasLimit (matching.diagram U)

attribute [instance] HasMatchingObjects.hasLimit

namespace HasMatchingObjects

/-- Limits of the matching-index shape supply matching objects. -/
@[stacks 0189 "matching objects from limits of the indexing shape"]
instance ofShape {n : ℕ}
    [HasLimitsOfShape (matching.index n) C] : HasMatchingObjects C n :=
  ⟨fun _ ↦ inferInstance⟩

end HasMatchingObjects

namespace matching

namespace diagram

/-- The matching diagram varies functorially with the truncated simplicial object. -/
@[stacks 0189 "matching-diagram functor"]
def functor (n : ℕ) :
    SimplicialObject.Truncated C n ⥤ matching.index n ⥤ C :=
  (Functor.whiskeringLeft (matching.index n)
    ((SimplexCategory.Truncated n)ᵒᵖ) C).obj
      (StructuredArrow.proj (op (SimplexCategory.mk (n + 1)))
        (SimplexCategory.Truncated.inclusion n).op)

/-- The matching-diagram functor evaluates to the canonical matching diagram. -/
@[simp, stacks 0189 "matching-diagram functor object"]
theorem functor_obj (n : ℕ) (U : SimplicialObject.Truncated C n) :
    (functor (C := C) n).obj U = matching.diagram U := sorry

/-- A map of matching diagrams is pointwise the corresponding component of the truncated
simplicial morphism. -/
@[simp, stacks 0189 "matching-diagram functor map"]
theorem functor_map_app {n : ℕ} {U V : SimplicialObject.Truncated C n}
    (α : U ⟶ V) (A : matching.index n) :
    ((functor (C := C) n).map α).app A = α.app A.right := sorry

end diagram

/-- The next-degree matching object of a truncated simplicial object. -/
@[stacks 0189 "canonical matching object"]
noncomputable abbrev object {n : ℕ} (U : SimplicialObject.Truncated C n)
    [HasLimit (matching.diagram U)] : C :=
  limit (matching.diagram U)

namespace object

/-- The canonical limit cone defining `matching.object U`. -/
@[stacks 0189 "matching-object limit cone"]
noncomputable def isLimit {n : ℕ} (U : SimplicialObject.Truncated C n)
    [HasLimit (matching.diagram U)] :
    IsLimit (limit.cone (matching.diagram U)) :=
  limit.isLimit _

/-- The projection from the matching object to an indexed face. -/
@[stacks 0189 "matching-object projection"]
noncomputable abbrev π {n : ℕ} (U : SimplicialObject.Truncated C n)
    [HasLimit (matching.diagram U)]
    (A : matching.index n) : object U ⟶ (matching.diagram U).obj A :=
  limit.π (matching.diagram U) A

/-- The canonical matching object represents the cone presheaf of its matching diagram. -/
@[stacks 0189 "matching-cone representability"]
noncomputable def coneRepresentableBy {n : ℕ} (U : SimplicialObject.Truncated C n)
    [HasLimit (matching.diagram U)] :
    (matching.diagram U).cones.RepresentableBy (object U) :=
  (isLimit U).representableBy

/-- The canonical matching object represents the explicit compatible face-family presheaf. -/
@[stacks 0189 "matching-family representability"]
noncomputable def representableBy {n : ℕ} (U : SimplicialObject.Truncated C n)
    [HasLimit (matching.diagram U)] :
    (FaceFamily.presheaf U).RepresentableBy (object U) :=
  (coneRepresentableBy U).ofIso (FaceFamily.coneIso U)

/-- The projection from the matching object to its `i`-th codimension-one face. -/
@[stacks 0189 "matching-object face projection"]
noncomputable abbrev face {n : ℕ} (U : SimplicialObject.Truncated C n)
    [HasLimit (matching.diagram U)] (i : Fin (n + 2)) :
    object U ⟶ U.obj (Opposite.op (⦋n⦌ₙ : SimplexCategory.Truncated n)) :=
  π U (matching.face i)

/-- The universal compatible face family carried by the canonical matching object. -/
@[stacks 0189 "universal matching face family"]
noncomputable def universalFamily {n : ℕ} (U : SimplicialObject.Truncated C n)
    [HasLimit (matching.diagram U)] : FaceFamily U (object U) :=
  (representableBy U).homEquiv (𝟙 (object U))

namespace representableBy

/-- The face family represented by a morphism into the matching object is obtained by
precomposing the universal family. -/
@[simp, stacks 0189 "matching-family representation formula"]
theorem homEquiv {n : ℕ} (U : SimplicialObject.Truncated C n)
    [HasLimit (matching.diagram U)] {X : C} (f : X ⟶ object U) :
    (matching.object.representableBy U).homEquiv f =
      (matching.object.universalFamily U).precomp f := sorry

end representableBy

/-- The coordinates of the universal face family are the canonical face projections. -/
@[simp, stacks 0189 "universal matching face coordinate"]
theorem universalFamily_app {n : ℕ} (U : SimplicialObject.Truncated C n)
    [HasLimit (matching.diagram U)] (i : Fin (n + 2)) :
    (universalFamily U).app i = face U i := sorry

end object

/-- A truncated simplicial morphism induces the canonical map between matching objects. Only
the two matching limits involved are required. -/
@[stacks 0189 "map of matching objects"]
noncomputable def map {n : ℕ} {U V : SimplicialObject.Truncated C n}
    [HasLimit (matching.diagram U)] [HasLimit (matching.diagram V)]
    (α : U ⟶ V) : object U ⟶ object V :=
  limMap ((diagram.functor (C := C) n).map α)

/-- The map of matching objects induced by an identity is the identity. -/
@[simp, stacks 0189 "identity map of matching objects"]
theorem map_id {n : ℕ} (U : SimplicialObject.Truncated C n)
    [HasLimit (matching.diagram U)] :
    map (𝟙 U) = 𝟙 (object U) := sorry

/-- Maps of matching objects preserve composition. -/
@[simp, stacks 0189 "composition of maps of matching objects"]
theorem map_comp {n : ℕ} {U V W : SimplicialObject.Truncated C n}
    [HasLimit (matching.diagram U)] [HasLimit (matching.diagram V)]
    [HasLimit (matching.diagram W)] (α : U ⟶ V) (β : V ⟶ W) :
    map (α ≫ β) = map α ≫ map β := sorry

/-- A map of matching objects commutes with every projection of the matching diagram. -/
@[reassoc (attr := simp), stacks 0189 "map of matching objects on projections"]
theorem map_π {n : ℕ} {U V : SimplicialObject.Truncated C n}
    [HasLimit (matching.diagram U)] [HasLimit (matching.diagram V)]
    (α : U ⟶ V) (A : matching.index n) :
    map α ≫ object.π V A = object.π U A ≫ α.app A.right := sorry

/-- A map of matching objects commutes with every codimension-one face projection. -/
@[reassoc (attr := simp), stacks 0189 "map of matching objects on faces"]
theorem map_face {n : ℕ} {U V : SimplicialObject.Truncated C n}
    [HasLimit (matching.diagram U)] [HasLimit (matching.diagram V)]
    (α : U ⟶ V) (i : Fin (n + 2)) :
    map α ≫ object.face V i =
      object.face U i ≫
        α.app (op (⦋n⦌ₙ : SimplexCategory.Truncated n)) := sorry

/-- The universal matching family is natural in the truncated simplicial object. -/
@[stacks 0189 "naturality of the universal matching family"]
theorem map_universalFamily {n : ℕ} {U V : SimplicialObject.Truncated C n}
    [HasLimit (matching.diagram U)] [HasLimit (matching.diagram V)]
    (α : U ⟶ V) :
    (object.universalFamily U).map α =
      (object.universalFamily V).precomp (map α) := sorry

/-- Matching objects form a functor whenever all matching limits at the fixed truncation level
exist. -/
@[stacks 0189 "matching-object functor"]
noncomputable def functor (n : ℕ) [HasMatchingObjects C n] :
    SimplicialObject.Truncated C n ⥤ C where
  obj U := object U
  map α := map α
  map_id U := matching.map_id U
  map_comp α β := matching.map_comp α β

/-- The matching-object functor evaluates to the canonical matching object. -/
@[simp, stacks 0189 "matching-object functor object"]
theorem functor_obj {n : ℕ} [HasMatchingObjects C n]
    (U : SimplicialObject.Truncated C n) :
    (functor (C := C) n).obj U = object U := sorry

/-- The matching-object functor maps a morphism by the canonical limit map. -/
@[simp, stacks 0189 "matching-object functor map"]
theorem functor_map {n : ℕ} [HasMatchingObjects C n]
    {U V : SimplicialObject.Truncated C n} (α : U ⟶ V) :
    (functor (C := C) n).map α = map α := sorry

namespace functor

/-- The projection at a matching index, natural in the truncated simplicial object. -/
@[stacks 0189 "natural matching-object projection"]
noncomputable def π {n : ℕ} [HasMatchingObjects C n] (A : matching.index n) :
    matching.functor (C := C) n ⟶
      (evaluation ((SimplexCategory.Truncated n)ᵒᵖ) C).obj A.right where
  app U := object.π U A
  naturality := fun {_ _} α ↦ map_π α A

/-- The component of the natural matching projection is the canonical limit projection. -/
@[simp, stacks 0189 "component of the natural matching projection"]
theorem π_app {n : ℕ} [HasMatchingObjects C n] (A : matching.index n)
    (U : SimplicialObject.Truncated C n) :
    (π (C := C) A).app U = object.π U A := sorry

/-- The `i`-th face projection, natural in the truncated simplicial object. -/
@[stacks 0189 "natural matching-object face projection"]
noncomputable def face {n : ℕ} [HasMatchingObjects C n] (i : Fin (n + 2)) :
    matching.functor (C := C) n ⟶
      (evaluation ((SimplexCategory.Truncated n)ᵒᵖ) C).obj
        (op (⦋n⦌ₙ : SimplexCategory.Truncated n)) :=
  π (C := C) (matching.face i)

/-- The component of the natural face projection is the canonical matching-object face. -/
@[simp, stacks 0189 "component of the natural matching face"]
theorem face_app {n : ℕ} [HasMatchingObjects C n] (i : Fin (n + 2))
    (U : SimplicialObject.Truncated C n) :
    (face (C := C) i).app U = object.face U i := sorry

/-- Naturality of the pointwise matching representations in the truncated simplicial object. -/
@[stacks 0189 "naturality of matching-family representations"]
theorem yonedaIso.naturality {n : ℕ} [HasMatchingObjects C n]
    {U V : SimplicialObject.Truncated C n} (α : U ⟶ V) :
    (matching.functor (C := C) n ⋙ yoneda).map α ≫
        (object.representableBy V).toIso.hom =
      (object.representableBy U).toIso.hom ≫
        (FaceFamily.presheaf.functor (C := C) n).map α := sorry

/-- The matching-object functor represents the face-family presheaf functor, naturally in the
truncated simplicial object. -/
@[stacks 0189 "natural representation of matching families"]
noncomputable def yonedaIso {n : ℕ} [HasMatchingObjects C n] :
    matching.functor (C := C) n ⋙ yoneda ≅
      FaceFamily.presheaf.functor (C := C) n :=
  NatIso.ofComponents (fun U ↦ (object.representableBy U).toIso)
    (fun {U V} α ↦ yonedaIso.naturality (C := C) (U := U) (V := V) α)

namespace yonedaIso

/-- A component of the natural matching representation is the canonical pointwise
represented-presheaf isomorphism. -/
@[simp, stacks 0189 "bundled component of the natural matching representation"]
theorem app {n : ℕ} [HasMatchingObjects C n]
    (U : SimplicialObject.Truncated C n) :
    (yonedaIso (C := C) (n := n)).app U =
      (object.representableBy U).toIso := sorry

/-- The component of `yonedaIso` is the canonical representation of matching families. -/
@[simp, stacks 0189 "component of the natural matching representation"]
theorem hom_app {n : ℕ} [HasMatchingObjects C n]
    (U : SimplicialObject.Truncated C n) :
    (yonedaIso (C := C) (n := n)).hom.app U =
      (object.representableBy U).toIso.hom := sorry

/-- The inverse component of the natural matching representation is the inverse of the chosen
pointwise representing isomorphism. -/
@[simp, stacks 0189 "inverse component of the natural matching representation"]
theorem inv_app {n : ℕ} [HasMatchingObjects C n]
    (U : SimplicialObject.Truncated C n) :
    (yonedaIso (C := C) (n := n)).inv.app U =
      (object.representableBy U).toIso.inv := sorry

end yonedaIso

end functor
end matching

end CategoryTheory.SimplicialObject.Truncated
