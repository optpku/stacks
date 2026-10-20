module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Relative.Action.Objects

/-!
# `2`-cell action of relative inertia

This leaf owns components, naturality, verticality, and vertical-composition laws for the action
of pseudo-comma `2`-morphisms. The local hom functor is assembled separately.
-/

@[expose] public section

universe u v u₁ v₁

namespace CategoryTheory
namespace BasedCategory

open BasedCategory BasedFunctor BasedNatIso BasedNatTrans
open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace RelativeInertia
namespace pseudoComma

variable
    {S T : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))}

noncomputable section

namespace map₂

namespace implementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- The left endpoint of a pseudo-comma `2`-morphism intertwines the automorphisms induced by
the two relative-inertia maps. -/
private theorem component_comm
    {f g : S ⟶ T} (η : f ⟶ g) (A : (relativeInertia S.hom).obj) :
    ((map f).toFunctor.obj A).aut.hom ≫
        (Bicategory.PseudoComma.left₂ η).toNatTrans.app A.obj =
      (Bicategory.PseudoComma.left₂ η).toNatTrans.app A.obj ≫
        ((map g).toFunctor.obj A).aut.hom := sorry

end implementation

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The component on a relative-inertia object of the `2`-cell action induced by a pseudo-comma
`2`-morphism. -/
@[stacks 04Z4 "component of the pseudo-comma relative-inertia action"]
def component {f g : S ⟶ T} (η : f ⟶ g) (A : (relativeInertia S.hom).obj) :
    (map f).toFunctor.obj A ⟶ (map g).toFunctor.obj A :=
  CategoryTheory.RelativeInertia.homMk
    ((Bicategory.ColaxComma.hom T).toFunctor :
      (Bicategory.ColaxComma.left T).obj ⥤
        (Bicategory.ColaxComma.right T).obj)
    ((Bicategory.PseudoComma.left₂ η).toNatTrans.app A.obj)
    (implementation.component_comm η A)

namespace component

/-- The relative-inertia components induced by a pseudo-comma `2`-morphism are natural in
relative-inertia morphisms. -/
@[reassoc, stacks 04Z4 "relative-inertia 2-cell naturality"]
theorem naturality
    {f g : S ⟶ T} (η : f ⟶ g)
    {A B : (relativeInertia S.hom).obj} (φ : A ⟶ B) :
    (map f).toFunctor.map φ ≫ component η B =
      component η A ≫ (map g).toFunctor.map φ := sorry

/-- The explicit relative-inertia component is vertical over the unchanged source-base object. -/
@[stacks 04Z4 "relative-inertia 2-cell component verticality"]
theorem isHomLift
    {f g : S ⟶ T} (η : f ⟶ g) (A : (relativeInertia S.hom).obj) :
    (relativeInertia T.hom).p.IsHomLift
      (𝟙 ((relativeInertia S.hom).p.obj A))
      (component η A) := sorry

end component

end map₂

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- A pseudo-comma `2`-morphism induces a based `2`-morphism between the corresponding maps on
relative inertia. -/
@[stacks 04Z4 "pseudo-comma relative-inertia action on 2-morphisms"]
def map₂ {f g : S ⟶ T} (η : f ⟶ g) : map f ⟶ map g where
  toNatTrans :=
    { app := map₂.component η
      naturality := fun {_ _} φ ↦ map₂.component.naturality η φ }
  isHomLift' := map₂.component.isHomLift η

namespace map₂

/-- Relative inertia preserves identity `2`-morphisms of pseudo-comma squares. -/
@[simp, stacks 04Z4 "relative-inertia 2-cell identity"]
theorem id (f : S ⟶ T) :
    map₂ (𝟙 f) = 𝟙 (map f) := sorry

/-- Relative inertia preserves vertical composition of pseudo-comma `2`-morphisms. -/
@[simp, stacks 04Z4 "relative-inertia 2-cell composition"]
theorem comp {f g h : S ⟶ T} (η : f ⟶ g) (θ : g ⟶ h) :
    map₂ (η ≫ θ) = map₂ η ≫ map₂ θ := sorry

end map₂

end

end pseudoComma
end RelativeInertia
end BasedCategory
end CategoryTheory
