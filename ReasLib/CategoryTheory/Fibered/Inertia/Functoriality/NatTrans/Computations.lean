/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Map.Computations
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.NatTrans.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Computations for the local `2`-cell action of based inertia

This leaf exposes component, underlying-arrow, naturality, local-functor, and induced-isomorphism
formulas without unfolding the concrete based transformations.
-/

@[expose] public section

universe u v u₁ v₁ u₂ v₂

namespace CategoryTheory
namespace BasedCategory

open BasedCategory BasedFunctor BasedNatIso BasedNatTrans

variable {C : Type u} [Category.{v} C]

namespace Inertia

variable {X : BasedCategory.{v₁, u₁} C}
variable {Y : BasedCategory.{v₂, u₂} C}
variable {F G : X ⥤ᵇ Y}

namespace map₂

/-- Evaluation of the inertia action is its canonical intertwined component. -/
@[simp, stacks 04Z4 "inertia two-cell component computation"]
theorem app (η : F ⟶ G) (A : (inertia X).obj) :
    (map₂ η).toNatTrans.app A = component η A := sorry

/-- The arrow underlying an inertia `2`-cell component is the original component. -/
@[simp, stacks 04Z4 "inertia two-cell underlying component"]
theorem app.underlying (η : F ⟶ G) (A : (inertia X).obj) :
    CategoryTheory.RelativeInertia.hom ((map₂ η).toNatTrans.app A) =
      η.toNatTrans.app A.obj := sorry

/-- Every packaged inertia `2`-cell component is vertical over the identity on the base. -/
theorem app.isHomLift (η : F ⟶ G) (A : (inertia X).obj) :
    (inertia Y).p.IsHomLift
      (𝟙 ((inertia X).p.obj A))
      ((map₂ η).toNatTrans.app A) := sorry

/-- The induced inertia `2`-morphism is natural in inertia morphisms. -/
@[reassoc, stacks 04Z4 "inertia two-cell packaged naturality"]
theorem naturality (η : F ⟶ G)
    {A B : (inertia X).obj} (φ : A ⟶ B) :
    (map F).toFunctor.map φ ≫ (map₂ η).toNatTrans.app B =
      (map₂ η).toNatTrans.app A ≫ (map G).toFunctor.map φ := sorry

/-- Two induced inertia `2`-morphisms agree when all of their components agree. -/
@[stacks 04Z4 "inertia two-cell extensionality"]
theorem ext {η θ : F ⟶ G}
    (h : ∀ A : (inertia X).obj,
      (map₂ η).toNatTrans.app A = (map₂ θ).toNatTrans.app A) :
    map₂ η = map₂ θ := sorry

end map₂

namespace mapFunctor

/-- The object action of the local inertia functor is the canonical inertia map. -/
@[simp, stacks 04Z4 "inertia hom-functor object computation"]
theorem obj (F : X ⥤ᵇ Y) :
    (mapFunctor X Y).obj F = map F := sorry

/-- The morphism action of the local inertia functor is the canonical inertia `2`-cell. -/
@[simp, stacks 04Z4 "inertia hom-functor map computation"]
theorem map (η : F ⟶ G) :
    (mapFunctor X Y).map η = map₂ η := sorry

/-- Evaluation of the local hom action is the packaged inertia `2`-cell component. -/
@[simp]
theorem map.app (η : F ⟶ G) (A : (inertia X).obj) :
    ((mapFunctor X Y).map η).toNatTrans.app A =
      (map₂ η).toNatTrans.app A := sorry

/-- The local hom action component has the original underlying arrow. -/
@[simp]
theorem map.app.underlying (η : F ⟶ G) (A : (inertia X).obj) :
    CategoryTheory.RelativeInertia.hom
        (((mapFunctor X Y).map η).toNatTrans.app A) =
      η.toNatTrans.app A.obj := sorry

/-- The local hom action component is vertical over the identity on the base. -/
theorem map.app.isHomLift (η : F ⟶ G) (A : (inertia X).obj) :
    (inertia Y).p.IsHomLift
      (𝟙 ((inertia X).p.obj A))
      (((mapFunctor X Y).map η).toNatTrans.app A) := sorry

end mapFunctor

namespace mapIso

/-- The forward `2`-morphism of the induced isomorphism is the forward inertia action. -/
@[simp, stacks 04Z4 "inertia map-isomorphism forward map"]
theorem hom (e : F ≅ G) :
    (mapIso e).hom = map₂ e.hom := sorry

/-- The inverse `2`-morphism of the induced isomorphism is the inverse inertia action. -/
@[simp, stacks 04Z4 "inertia map-isomorphism inverse map"]
theorem inv (e : F ≅ G) :
    (mapIso e).inv = map₂ e.inv := sorry

/-- The forward component of an induced inertia isomorphism is the canonical intertwined
component. -/
@[simp, stacks 04Z4 "inertia map-isomorphism forward component"]
theorem hom.app (e : F ≅ G) (A : (inertia X).obj) :
    (mapIso e).hom.toNatTrans.app A = map₂.component e.hom A := sorry

/-- The inverse component of an induced inertia isomorphism is the canonical reverse
intertwined component. -/
@[simp, stacks 04Z4 "inertia map-isomorphism inverse component"]
theorem inv.app (e : F ≅ G) (A : (inertia X).obj) :
    (mapIso e).inv.toNatTrans.app A = map₂.component e.inv A := sorry

/-- The arrow underlying a forward induced-isomorphism component is the original forward
component. -/
@[simp, stacks 04Z4 "inertia map-isomorphism forward underlying component"]
theorem hom.app.underlying (e : F ≅ G) (A : (inertia X).obj) :
    CategoryTheory.RelativeInertia.hom ((mapIso e).hom.toNatTrans.app A) =
      e.hom.toNatTrans.app A.obj := sorry

/-- The arrow underlying an inverse induced-isomorphism component is the original inverse
component. -/
@[simp, stacks 04Z4 "inertia map-isomorphism inverse underlying component"]
theorem inv.app.underlying (e : F ≅ G) (A : (inertia X).obj) :
    CategoryTheory.RelativeInertia.hom ((mapIso e).inv.toNatTrans.app A) =
      e.inv.toNatTrans.app A.obj := sorry

/-- Every forward component of an induced inertia isomorphism is vertical over the identity on
the base. -/
theorem hom.app.isHomLift (e : F ≅ G) (A : (inertia X).obj) :
    (inertia Y).p.IsHomLift
      (𝟙 ((inertia X).p.obj A))
      ((mapIso e).hom.toNatTrans.app A) := sorry

/-- Every inverse component of an induced inertia isomorphism is vertical over the identity on
the base. -/
theorem inv.app.isHomLift (e : F ≅ G) (A : (inertia X).obj) :
    (inertia Y).p.IsHomLift
      (𝟙 ((inertia X).p.obj A))
      ((mapIso e).inv.toNatTrans.app A) := sorry

end mapIso

end Inertia

end BasedCategory
end CategoryTheory
