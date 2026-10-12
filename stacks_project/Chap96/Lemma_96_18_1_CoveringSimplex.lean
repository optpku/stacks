/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalIso
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Equivalence
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic

/-!
# Covering simplices of a 1-morphism of categories fibred in groupoids

The category `U_n` attached to a 1-morphism `f : U ⟶ X` of categories fibred in
groupoids, with projection `f_n : U_n ⟶ X` and strictly functorial operators `U_φ`.
-/

@[expose] public section

open CategoryTheory
open scoped Bicategory Simplicial

noncomputable section

universe u v w vS

namespace CategoryTheory.FiberedCategoryOver.Groupoids.Cech

variable {C : Type u} [Category.{v} C]
variable {U X : FiberedCategoryOver.Groupoids C}

namespace Simplex

/-- An object of the covering simplex `U_n`: vertices in `U`, an apex in `X`, and
isomorphisms `f(u_i) ≅ x`. -/
structure Obj (f : U ⟶ X) (n : SimplexCategory) where
  /-- The `n.len + 1` vertices in the total category of `U`. -/
  vertices : Fin (n.len + 1) → U.total
  /-- The common apex in the total category of `X`. -/
  apex : X.total
  /-- The isomorphisms `f(u_i) ≅ x`. -/
  iso : ∀ i : Fin (n.len + 1), (toFunctor f).obj (vertices i) ≅ apex

/-- A morphism of covering-simplex objects: vertex maps and an apex map compatible
with the structure isomorphisms. -/
structure Hom {f : U ⟶ X} {n : SimplexCategory} (P Q : Obj f n) where
  /-- The maps on vertices. -/
  vertex : ∀ i : Fin (n.len + 1), P.vertices i ⟶ Q.vertices i
  /-- The map on apices. -/
  apex : P.apex ⟶ Q.apex
  /-- Compatibility of vertex maps with the structure isomorphisms. -/
  comm : ∀ i : Fin (n.len + 1),
    (toFunctor f).map (vertex i) ≫ (Q.iso i).hom = (P.iso i).hom ≫ apex

/-- Constructor for covering-simplex objects from vertices, an apex, and structure
isomorphisms. -/
def objMk {f : U ⟶ X} {n : SimplexCategory}
    (vertices : Fin (n.len + 1) → U.total) (apex : X.total)
    (iso : ∀ i : Fin (n.len + 1), (toFunctor f).obj (vertices i) ≅ apex) :
    Obj f n :=
  ⟨vertices, apex, iso⟩

/-- Constructor for covering-simplex morphisms from vertex maps, an apex map, and
the compatibility condition. -/
def homMk {f : U ⟶ X} {n : SimplexCategory} {P Q : Obj f n}
    (vertex : ∀ i : Fin (n.len + 1), P.vertices i ⟶ Q.vertices i)
    (apex : P.apex ⟶ Q.apex)
    (comm : ∀ i : Fin (n.len + 1),
      (toFunctor f).map (vertex i) ≫ (Q.iso i).hom = (P.iso i).hom ≫ apex) :
    Hom P Q :=
  ⟨vertex, apex, comm⟩

/-- Covering-simplex objects are determined by vertices, apex, and structure
isomorphisms. -/
@[ext (iff := false)]
theorem ext {f : U ⟶ X} {n : SimplexCategory} {P Q : Obj f n}
    (hvertices : P.vertices = Q.vertices) (hapex : P.apex = Q.apex)
    (hiso : HEq P.iso Q.iso) : P = Q := sorry

/-- Covering-simplex morphisms are determined by their vertex and apex maps. -/
@[ext]
theorem hom_ext {f : U ⟶ X} {n : SimplexCategory} {P Q : Obj f n} {φ ψ : Hom P Q}
    (hvertex : φ.vertex = ψ.vertex) (hapex : φ.apex = ψ.apex) : φ = ψ := sorry

/-- Identity morphism of a covering-simplex object. -/
def id {f : U ⟶ X} {n : SimplexCategory} (P : Obj f n) : Hom P P :=
  homMk (fun i ↦ 𝟙 (P.vertices i)) (𝟙 P.apex) sorry

/-- Composition of covering-simplex morphisms. -/
def comp {f : U ⟶ X} {n : SimplexCategory} {P Q R : Obj f n}
    (φ : Hom P Q) (ψ : Hom Q R) : Hom P R :=
  homMk (fun i ↦ φ.vertex i ≫ ψ.vertex i) (φ.apex ≫ ψ.apex) sorry

/-- Covering-simplex objects form a category. -/
instance category (f : U ⟶ X) (n : SimplexCategory) : Category.{vS} (Obj f n) where
  Hom := Hom
  id := id
  comp := comp
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

end Simplex

/-- The functor sending a covering-simplex object to its apex in `X`. -/
def apexFunctor (f : U ⟶ X) (n : SimplexCategory) : Simplex.Obj f n ⥤ X.total where
  obj P := P.apex
  map φ := φ.apex
  map_id := sorry
  map_comp := sorry

/-- The projection of `U_n` to the base category `C`, via the apex. -/
def projectionFunctor (f : U ⟶ X) (n : SimplexCategory) : Simplex.Obj f n ⥤ C :=
  apexFunctor f n ⋙ X.p

/-- The covering simplex `U_n` is fibred in groupoids over `C`. -/
instance projectionFunctor.fiberedInGroupoids (f : U ⟶ X) (n : SimplexCategory) :
    Functor.IsFibered.InGroupoids (projectionFunctor f n) := sorry

/-- The covering simplex `U_n` as a category fibred in groupoids over `C`. -/
def covering (f : U ⟶ X) (n : SimplexCategory) : FiberedCategoryOver.Groupoids C :=
  ofFunctor (projectionFunctor f n)

/-- The projection `f_n : U_n ⟶ X` sending a covering-simplex object to its apex. -/
def proj (f : U ⟶ X) (n : SimplexCategory) : covering f n ⟶ X :=
  ofBasedFunctor
    { toFunctor := apexFunctor f n
      w := sorry }

/-- Reindexing of covering-simplex objects along a morphism of simplices. -/
def reindex {f : U ⟶ X} {m n : SimplexCategory} (φ : m ⟶ n) :
    Simplex.Obj f n ⥤ Simplex.Obj f m where
  obj P := Simplex.objMk (fun i ↦ P.vertices (φ.toOrderHom i)) P.apex
    (fun i ↦ P.iso (φ.toOrderHom i))
  map ψ := Simplex.homMk (fun i ↦ ψ.vertex (φ.toOrderHom i)) ψ.apex sorry
  map_id := sorry
  map_comp := sorry

/-- The 1-morphism `U_φ : U_n ⟶ U_m` induced by `φ : m ⟶ n`. -/
def simplexMap {f : U ⟶ X} {m n : SimplexCategory} (φ : m ⟶ n) :
    covering f n ⟶ covering f m :=
  ofBasedFunctor
    { toFunctor := reindex φ
      w := sorry }

/-- Simplicial identity: `U_id` is the identity 1-morphism of `U_n`. -/
theorem simplexMap_id (f : U ⟶ X) (n : SimplexCategory) :
    simplexMap (CategoryStruct.id n) = 𝟙 (covering f n) := sorry

/-- Simplicial identity: `U_{φ ≫ ψ} = U_ψ ≫ U_φ`. -/
theorem simplexMap_comp {f : U ⟶ X} {m n p : SimplexCategory} (φ : m ⟶ n) (ψ : n ⟶ p) :
    simplexMap (CategoryStruct.comp φ ψ) =
      (simplexMap ψ ≫ simplexMap φ : covering f p ⟶ covering f m) := sorry

/-- The total-category functor `U ⟶ U_0` sending `u` to `(u, f(u), refl)`. -/
def degreeZeroToFunctor (f : U ⟶ X) :
    U.total ⥤ Simplex.Obj f (SimplexCategory.mk 0) where
  obj u := Simplex.objMk (fun _ ↦ u) ((toFunctor f).obj u) (fun _ ↦ Iso.refl _)
  map φ := Simplex.homMk (fun _ ↦ φ) ((toFunctor f).map φ) sorry
  map_id := sorry
  map_comp := sorry

/-- The 1-morphism `U ⟶ U_0` sending `u` to `(u, f(u), refl)`. -/
def degreeZeroTo (f : U ⟶ X) : U ⟶ covering f (SimplexCategory.mk 0) :=
  ofBasedFunctor
    { toFunctor := degreeZeroToFunctor f
      w := sorry }

/-- Objectwise isomorphism identifying `(u_0, f(u_0), refl)` with a general object of `U_0`. -/
def degreeZeroObjIso (f : U ⟶ X) (P : Simplex.Obj f (SimplexCategory.mk 0)) :
    (degreeZeroToFunctor f).obj (P.vertices 0) ≅ P where
  hom := Simplex.homMk
    (fun i ↦ eqToHom (congrArg P.vertices (Fin.eq_zero i).symm)) (P.iso 0).hom sorry
  inv := Simplex.homMk
    (fun i ↦ eqToHom (congrArg P.vertices (Fin.eq_zero i))) (P.iso 0).inv sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The degree-zero comparison identifies `f` with `degreeZeroTo ≫ proj`. -/
def degreeZeroTo_proj (f : U ⟶ X) :
    degreeZeroTo f ≫ proj f (SimplexCategory.mk 0) ≅ f :=
  BasedFunctorIso.lift
    (BasedNatIso.ofComponents (fun _ ↦ Iso.refl _) sorry sorry)

/-- The 1-morphism `U ⟶ U_0` is an equivalence of categories fibred in groupoids. -/
theorem degreeZeroTo_isEquivalence (f : U ⟶ X) :
    BasedFunctor.IsEquivalence (toBasedFunctor (degreeZeroTo f)) := sorry

end CategoryTheory.FiberedCategoryOver.Groupoids.Cech
