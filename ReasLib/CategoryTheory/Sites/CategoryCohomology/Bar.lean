/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bar complexes for category cohomology

This file owns the composable-arrow cosimplicial resolution of an additive presheaf.  The
construction is independent of a Grothendieck topology and of derived functors; comparison with
right-derived limits is kept in a separate leaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v w

namespace CategoryTheory.CategoryCohomology.Bar

variable {C : Type u} [Category.{v} C]
variable [UnivLE.{max u v, w}]

/-- A simplex of the category-cohomology bar construction is a composable chain in `C`. -/
abbrev Chain (C : Type u) [Category.{v} C] (Delta : SimplexCategory) :=
  ComposableArrows C Delta.len

/-- The initial object of a composable chain. -/
abbrev firstObject (C : Type u) [Category.{v} C]
    {Delta : SimplexCategory} (x : Chain C Delta) : C :=
  x.obj 0

/-- Precomposition of a composable chain by a simplex morphism. -/
abbrev precomp (C : Type u) [Category.{v} C]
    {Delta Delta' : SimplexCategory} (f : Delta ⟶ Delta') (x : Chain C Delta') :
    Chain C Delta :=
  (nerve C).map f.op x

/-- The morphism from the initial object of a chain to the initial object of its precomposition. -/
abbrev initialMap (C : Type u) [Category.{v} C]
    {Delta Delta' : SimplexCategory} (f : Delta ⟶ Delta') (x : Chain C Delta') :
    firstObject C x ⟶ firstObject C (precomp C f x) :=
  x.map (show (0 : Fin (Delta'.len + 1)) ⟶ f.toOrderHom 0 from
    homOfLE (Fin.zero_le _))

/-- Precomposition by an identity simplex morphism fixes a chain. -/
@[simp, stacks 08RZ "category-cohomology chain identity"]
theorem precomp_id {Delta : SimplexCategory} (x : Chain C Delta) :
    precomp C (𝟙 Delta) x = x := sorry

/-- Precomposition of category-cohomology chains respects composition. -/
@[simp, stacks 08RZ "category-cohomology chain composition"]
theorem precomp_comp {Delta₀ Delta₁ Delta₂ : SimplexCategory}
    (f : Delta₀ ⟶ Delta₁) (g : Delta₁ ⟶ Delta₂) (x : Chain C Delta₂) :
    precomp C (f ≫ g) x = precomp C f (precomp C g x) := sorry

/-- The initial-object map associated to an identity simplex morphism is the identity. -/
@[simp, stacks 08RZ "category-cohomology initial-map identity"]
theorem initialMap_id {Delta : SimplexCategory} (x : Chain C Delta) :
    initialMap C (𝟙 Delta) x = 𝟙 (firstObject C x) := sorry

/-- Initial-object maps compose contravariantly with simplex morphisms. -/
@[stacks 08RZ "category-cohomology initial-map composition"]
theorem initialMap_comp {Delta₀ Delta₁ Delta₂ : SimplexCategory}
    (f : Delta₀ ⟶ Delta₁) (g : Delta₁ ⟶ Delta₂) (x : Chain C Delta₂) :
    initialMap C (f ≫ g) x =
      initialMap C g x ≫ initialMap C f (precomp C g x) := sorry

/-- The cosimplicial additive group whose value at a simplex is the product of `F` at the initial
objects of all composable chains of that shape. -/
@[stacks 08RZ "category-cohomology bar cosimplicial object"]
noncomputable def cosimplicialObject (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) :
    CosimplicialObject AddCommGrpCat.{w} where
  obj Delta := ∏ᶜ fun x : Chain C Delta => F.obj (op (firstObject C x))
  map f := Pi.lift fun x =>
    Pi.π (fun y : Chain C _ => F.obj (op (firstObject C y))) (precomp C f x) ≫
      F.map (initialMap C f x).op
  map_id := sorry
  map_comp := sorry

/-- The cosimplicial structure map is computed projectionwise by restriction along the
initial-object map of a chain. -/
@[simp, stacks 08RZ "category-cohomology cosimplicial projection formula"]
theorem cosimplicialObject_map_π (F : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    {Delta Delta' : SimplexCategory} (f : Delta ⟶ Delta') (x : Chain C Delta') :
    (cosimplicialObject F).map f ≫
        Pi.π (fun y : Chain C Delta' => F.obj (op (firstObject C y))) x =
      Pi.π (fun y : Chain C Delta => F.obj (op (firstObject C y))) (precomp C f x) ≫
        F.map (initialMap C f x).op := sorry

/-- The component of the cosimplicial bar map induced by a coefficient morphism. -/
abbrev mapApp {F G : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (eta : F ⟶ G)
    (Delta : SimplexCategory) :
    (cosimplicialObject F).obj Delta ⟶ (cosimplicialObject G).obj Delta :=
  Pi.lift fun x =>
    Pi.π (fun y : Chain C Delta => F.obj (op (firstObject C y))) x ≫
      eta.app (op (firstObject C x))

/-- Naturality of the cosimplicial bar map induced by a coefficient morphism. -/
@[stacks 08RZ "category-cohomology bar-map naturality"]
theorem map_naturality {F G : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (eta : F ⟶ G)
    {Delta Delta' : SimplexCategory} (f : Delta ⟶ Delta') :
    (cosimplicialObject F).map f ≫ mapApp eta Delta' =
      mapApp eta Delta ≫ (cosimplicialObject G).map f := sorry

/-- The cosimplicial bar map induced by a coefficient morphism. -/
@[stacks 08RZ "category-cohomology cosimplicial bar map"]
noncomputable def cosimplicialMap {F G : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (eta : F ⟶ G) :
    cosimplicialObject F ⟶ cosimplicialObject G where
  app := mapApp eta
  naturality := fun _ _ f => map_naturality eta f

/-- A coefficient morphism acts componentwise on every product in the cosimplicial bar
construction. -/
@[simp, stacks 08RZ "category-cohomology coefficient-map projection formula"]
theorem cosimplicialMap_app_π {F G : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (eta : F ⟶ G)
    (Delta : SimplexCategory) (x : Chain C Delta) :
    (cosimplicialMap eta).app Delta ≫
        Pi.π (fun y : Chain C Delta => G.obj (op (firstObject C y))) x =
      Pi.π (fun y : Chain C Delta => F.obj (op (firstObject C y))) x ≫
        eta.app (op (firstObject C x)) := sorry

/-- The identity coefficient morphism induces the identity cosimplicial bar map. -/
@[simp, stacks 08RZ "category-cohomology cosimplicial identity map"]
theorem cosimplicialMap_id (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) :
    cosimplicialMap (𝟙 F) = 𝟙 (cosimplicialObject F) := sorry

/-- Cosimplicial bar maps respect composition of coefficient morphisms. -/
@[simp, stacks 08RZ "category-cohomology cosimplicial composition map"]
theorem cosimplicialMap_comp {F G H : Cᵒᵖ ⥤ AddCommGrpCat.{w}}
    (f : F ⟶ G) (g : G ⟶ H) :
    cosimplicialMap (f ≫ g) = cosimplicialMap f ≫ cosimplicialMap g := sorry

/-- The composable-arrow cosimplicial construction as a functor of additive presheaves. -/
@[stacks 08RZ "functorial category-cohomology cosimplicial bar construction"]
noncomputable def cosimplicialFunctor :
    (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ CosimplicialObject AddCommGrpCat.{w} where
  obj := cosimplicialObject
  map := cosimplicialMap
  map_id := cosimplicialMap_id
  map_comp := cosimplicialMap_comp

/-- The category-cohomology bar complex as a functor of additive presheaves. -/
@[stacks 08RZ "functorial category-cohomology bar complex"]
noncomputable abbrev complexFunctor :
    (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ CochainComplex AddCommGrpCat.{w} ℕ :=
  cosimplicialFunctor (C := C) ⋙
    AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{w}

/-- The explicit category-cohomology bar complex of an additive presheaf. -/
@[stacks 08RZ "category-cohomology bar complex"]
noncomputable abbrev complex (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) :
    CochainComplex AddCommGrpCat.{w} ℕ :=
  (complexFunctor (C := C)).obj F

/-- The degree-`n` cohomology functor of the category-cohomology bar complex. -/
@[stacks 08RZ "category-cohomology bar cohomology functor"]
noncomputable abbrev cohomologyFunctor (n : ℕ) :
    (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w} :=
  complexFunctor (C := C) ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat.{w} (ComplexShape.up ℕ) n

/-- The degree-`n` cohomology object of the category-cohomology bar complex. -/
@[stacks 08RZ "category-cohomology bar cohomology object"]
noncomputable abbrev cohomology (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    AddCommGrpCat.{w} :=
  (cohomologyFunctor (C := C) n).obj F

/-- The category-cohomology bar complex functor is additive. -/
@[stacks 08RZ "additivity of the category-cohomology bar complex"]
instance complexFunctor.additive : (complexFunctor (C := C)).Additive := sorry

/-- The category-cohomology bar complex functor is exact in its coefficient presheaf. -/
@[stacks 08RZ "exactness of the category-cohomology bar complex"]
theorem complexFunctor_exact :
    exactFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{w})
      (CochainComplex AddCommGrpCat.{w} ℕ) (complexFunctor (C := C)) := sorry

/-- The category-cohomology bar complex bundled as an exact functor. -/
@[stacks 08RZ "bundled exact category-cohomology bar complex"]
noncomputable def complexExactFunctor :
    (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ₑ CochainComplex AddCommGrpCat.{w} ℕ :=
  ⟨complexFunctor (C := C), complexFunctor_exact (C := C)⟩

end CategoryTheory.CategoryCohomology.Bar
