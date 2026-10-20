module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Map.Relative.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Relative.Action.Construction

/-!
# Local action of fibred relative inertia

This file owns the reusable `1`- and `2`-morphism data of relative inertia on
the pseudo-comma bicategory.  The corresponding readout and functoriality
lemmas are in `Relative.Action.Computations`.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open Bicategory
open scoped Bicategory

namespace FiberedCategoryOver.RelativeInertia.pseudoComma

variable {C : Type u} [Category.{v} C]

variable
    {S T : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))}

noncomputable section

/-- An invertibly commuting square of fibred functors induces the canonical cartesian map
between the corresponding relative-inertia fibrations. -/
def map (f : S ⟶ T) :
    FiberedCategoryOver.relativeInertia S.hom ⟶
      FiberedCategoryOver.relativeInertia T.hom :=
  FiberedCategoryOver.RelativeInertia.map
    (Bicategory.PseudoComma.left f) (Bicategory.PseudoComma.right f)
    (Bicategory.PseudoComma.cellIso f).symm

namespace map₂

namespace implementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- The left endpoint of a fibred pseudo-comma `2`-morphism intertwines the automorphisms
induced by the two relative-inertia maps. -/
private theorem component_comm
    {f g : S ⟶ T} (eta : f ⟶ g)
    (A : (FiberedCategoryOver.relativeInertia S.hom).total) :
    ((FiberedCategoryOver.toFunctor (map f)).obj A).aut.hom ≫
        (FiberedCategoryOver.toNatTrans
          (Bicategory.PseudoComma.left₂ eta)).app A.obj =
      (FiberedCategoryOver.toNatTrans
          (Bicategory.PseudoComma.left₂ eta)).app A.obj ≫
        ((FiberedCategoryOver.toFunctor (map g)).obj A).aut.hom := sorry

end implementation

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The component of the fibred relative-inertia action on a pseudo-comma `2`-morphism. -/
def component {f g : S ⟶ T} (eta : f ⟶ g)
    (A : (FiberedCategoryOver.relativeInertia S.hom).total) :
    (FiberedCategoryOver.toFunctor (map f)).obj A ⟶
      (FiberedCategoryOver.toFunctor (map g)).obj A :=
  CategoryTheory.RelativeInertia.homMk
    (FiberedCategoryOver.toFunctor T.hom)
    ((FiberedCategoryOver.toNatTrans
      (Bicategory.PseudoComma.left₂ eta)).app A.obj)
    (implementation.component_comm eta A)

namespace implementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- The explicit fibred relative-inertia components are natural in relative-inertia
morphisms. -/
private theorem component_naturality
    {f g : S ⟶ T} (eta : f ⟶ g)
    {A B : (FiberedCategoryOver.relativeInertia S.hom).total} (phi : A ⟶ B) :
    (FiberedCategoryOver.toFunctor (map f)).map phi ≫ component eta B =
      component eta A ≫ (FiberedCategoryOver.toFunctor (map g)).map phi := sorry

/-- The explicit fibred relative-inertia component is vertical over the unchanged base
object. -/
private theorem component_isHomLift
    {f g : S ⟶ T} (eta : f ⟶ g)
    (A : (FiberedCategoryOver.relativeInertia S.hom).total) :
    (FiberedCategoryOver.relativeInertia T.hom).p.IsHomLift
      (𝟙 ((FiberedCategoryOver.relativeInertia S.hom).p.obj A))
      (component eta A) := sorry

end implementation

end map₂

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The based natural transformation underlying the fibred relative-inertia action on a
pseudo-comma `2`-morphism. -/
def map₂.basedNatTrans {f g : S ⟶ T} (eta : f ⟶ g) :
    FiberedCategoryOver.toBasedFunctor (map f) ⟶
      FiberedCategoryOver.toBasedFunctor (map g) where
  toNatTrans :=
    { app := map₂.component eta
      naturality := fun {_ _} phi =>
        map₂.implementation.component_naturality eta phi }
  isHomLift' := map₂.implementation.component_isHomLift eta

/-- A pseudo-comma `2`-morphism induces the canonical `2`-morphism between its cartesian
relative-inertia maps. -/
def map₂ {f g : S ⟶ T} (eta : f ⟶ g) : map f ⟶ map g :=
  FiberedCategoryOver.ofBasedNatTrans (map₂.basedNatTrans eta)

namespace map₂

/-- Fibred relative inertia preserves identity pseudo-comma `2`-morphisms. -/
@[simp]
theorem id (f : S ⟶ T) :
    map₂ (𝟙 f) = 𝟙 (map f) := sorry

/-- Fibred relative inertia preserves vertical composition of pseudo-comma `2`-morphisms. -/
@[simp]
theorem comp {f g h : S ⟶ T} (eta : f ⟶ g) (theta : g ⟶ h) :
    map₂ (eta ≫ theta) = map₂ eta ≫ map₂ theta := sorry

end map₂

/-!
The construction above is intentionally split at the based layer: `map₂.basedNatTrans` owns the
concrete components, while `map₂` only restores the fibred hom-property witness.
-/

end

end FiberedCategoryOver.RelativeInertia.pseudoComma
end CategoryTheory
