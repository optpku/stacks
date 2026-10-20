module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import Mathlib.CategoryTheory.Pi.Basic
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

/-- Covering simplices are the categorical pullback of componentwise application
of the covering morphism and the diagonal on its target. -/
abbrev Obj (f : U ⟶ X) (n : SimplexCategory) :=
  Limits.CategoricalPullback
    (Functor.pi (fun _ : Fin (n.len + 1) ↦ toFunctor f))
    (Functor.pi' (fun _ : Fin (n.len + 1) ↦ Functor.id X.total))

/-- The vertices of a covering simplex. -/
def Obj.vertices {f : U ⟶ X} {n : SimplexCategory} (P : Obj f n) :
    Fin (n.len + 1) → U.total := P.fst

/-- The common apex of a covering simplex. -/
def Obj.apex {f : U ⟶ X} {n : SimplexCategory} (P : Obj f n) : X.total := P.snd

/-- The component structure isomorphisms of a covering simplex. -/
def Obj.iso {f : U ⟶ X} {n : SimplexCategory} (P : Obj f n)
    (i : Fin (n.len + 1)) : (toFunctor f).obj (P.vertices i) ≅ P.apex :=
  Pi.isoApp (Limits.CategoricalPullback.iso P) i

/-- Morphisms of covering simplices are the inherited categorical-pullback morphisms. -/
abbrev Hom {f : U ⟶ X} {n : SimplexCategory} (P Q : Obj f n) := P ⟶ Q

/-- The component vertex maps of a morphism of covering simplices. -/
def Hom.vertex {f : U ⟶ X} {n : SimplexCategory} {P Q : Obj f n} (φ : Hom P Q) :
    ∀ i : Fin (n.len + 1), P.vertices i ⟶ Q.vertices i := φ.fst

/-- The apex map of a morphism of covering simplices. -/
def Hom.apex {f : U ⟶ X} {n : SimplexCategory} {P Q : Obj f n} (φ : Hom P Q) :
    P.apex ⟶ Q.apex := φ.snd

/-- Vertex and apex maps commute with each component structure isomorphism. -/
theorem Hom.comm {f : U ⟶ X} {n : SimplexCategory} {P Q : Obj f n} (φ : Hom P Q)
    (i : Fin (n.len + 1)) :
    (toFunctor f).map (φ.vertex i) ≫ (Q.iso i).hom = (P.iso i).hom ≫ φ.apex :=
  congrFun φ.w i

/-- Construct a covering simplex from vertices, an apex, and structure isomorphisms. -/
def objMk {f : U ⟶ X} {n : SimplexCategory}
    (vertices : Fin (n.len + 1) → U.total) (apex : X.total)
    (iso : ∀ i : Fin (n.len + 1), (toFunctor f).obj (vertices i) ≅ apex) :
    Obj f n :=
  ⟨vertices, apex, Pi.isoMk iso⟩

/-- Construct a covering-simplex morphism from compatible vertex and apex maps. -/
def homMk {f : U ⟶ X} {n : SimplexCategory} {P Q : Obj f n}
    (vertex : ∀ i : Fin (n.len + 1), P.vertices i ⟶ Q.vertices i)
    (apex : P.apex ⟶ Q.apex)
    (comm : ∀ i : Fin (n.len + 1),
      (toFunctor f).map (vertex i) ≫ (Q.iso i).hom = (P.iso i).hom ≫ apex) :
    Hom P Q :=
  ⟨vertex, apex, funext comm⟩

/-- Covering-simplex objects are determined by vertices, apex, and structure
isomorphisms. -/
@[ext (iff := false)]
theorem ext {f : U ⟶ X} {n : SimplexCategory} {P Q : Obj f n}
    (hvertices : P.vertices = Q.vertices) (hapex : P.apex = Q.apex)
    (hiso : HEq P.iso Q.iso) : P = Q := sorry

end Simplex

end CategoryTheory.FiberedCategoryOver.Groupoids.Cech

namespace CategoryTheory.Limits.CategoricalPullback.Hom

export CategoryTheory.FiberedCategoryOver.Groupoids.Cech.Simplex.Hom (vertex apex comm)

end CategoryTheory.Limits.CategoricalPullback.Hom

namespace CategoryTheory.FiberedCategoryOver.Groupoids.Cech

variable {C : Type u} [Category.{v} C]
variable {U X : FiberedCategoryOver.Groupoids C}

/-- The functor sending a covering-simplex object to its apex in `X`. -/
def apexFunctor (f : U ⟶ X) (n : SimplexCategory) : Simplex.Obj f n ⥤ X.total :=
  Limits.CategoricalPullback.π₂ _ _

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
    Simplex.Obj f n ⥤ Simplex.Obj f m := by
  refine {
    obj P := Simplex.objMk (fun i ↦ P.vertices (φ.toOrderHom i)) P.apex
      (fun i ↦ P.iso (φ.toOrderHom i))
    map ψ := Simplex.homMk (fun i ↦ ψ.vertex (φ.toOrderHom i)) ψ.apex ?_
    map_id := ?_
    map_comp := ?_
  }
  all_goals sorry

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
    U.total ⥤ Simplex.Obj f (SimplexCategory.mk 0) := by
  refine {
    obj u := Simplex.objMk (fun _ ↦ u) ((toFunctor f).obj u) (fun _ ↦ Iso.refl _)
    map φ := Simplex.homMk (fun _ ↦ φ) ((toFunctor f).map φ) ?_
    map_id := ?_
    map_comp := ?_
  }
  all_goals sorry

/-- The 1-morphism `U ⟶ U_0` sending `u` to `(u, f(u), refl)`. -/
def degreeZeroTo (f : U ⟶ X) : U ⟶ covering f (SimplexCategory.mk 0) :=
  ofBasedFunctor
    { toFunctor := degreeZeroToFunctor f
      w := sorry }

/-- Objectwise isomorphism identifying `(u_0, f(u_0), refl)` with a general object of `U_0`. -/
def degreeZeroObjIso (f : U ⟶ X) (P : Simplex.Obj f (SimplexCategory.mk 0)) :
    (degreeZeroToFunctor f).obj (P.vertices 0) ≅ P := by
  refine {
    hom := Simplex.homMk
      (fun i ↦ eqToHom (congrArg P.vertices (Fin.eq_zero i).symm)) (P.iso 0).hom ?_
    inv := Simplex.homMk
      (fun i ↦ eqToHom (congrArg P.vertices (Fin.eq_zero i))) (P.iso 0).inv ?_
    hom_inv_id := ?_
    inv_hom_id := ?_
  }
  all_goals sorry

/-- The degree-zero comparison identifies `f` with `degreeZeroTo ≫ proj`. -/
def degreeZeroTo_proj (f : U ⟶ X) :
    degreeZeroTo f ≫ proj f (SimplexCategory.mk 0) ≅ f := by
  refine BasedFunctorIso.lift
    (BasedNatIso.ofComponents (fun _ ↦ Iso.refl _) ?_ ?_)
  all_goals sorry

/-- The 1-morphism `U ⟶ U_0` is an equivalence of categories fibred in groupoids. -/
instance degreeZeroTo_isEquivalence (f : U ⟶ X) :
    BasedFunctor.IsEquivalence (toBasedFunctor (degreeZeroTo f)) := sorry

end CategoryTheory.FiberedCategoryOver.Groupoids.Cech
