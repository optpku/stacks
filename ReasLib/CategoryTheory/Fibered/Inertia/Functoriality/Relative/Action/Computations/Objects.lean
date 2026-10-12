/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Relative.Action.Objects
import Mathlib.Tactic.CrossRefAttribute

/-!
# Object and `1`-cell computations for relative inertia

This leaf exposes the total-functor, object, automorphism, and arrow readouts of the
pseudo-comma relative-inertia map.
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

/-- The underlying total functor of the pseudo-comma relative-inertia map is the map associated
to the square formed by its two endpoint maps and its inverted comparison cell. -/
@[simp, stacks 04Z4 "relative inertia action total computation"]
theorem map.toFunctor (f : S ⟶ T) :
    (map f).toFunctor =
      CategoryTheory.RelativeInertia.map
        (Bicategory.PseudoComma.left f).toFunctor
        (Bicategory.PseudoComma.right f).toFunctor
        (BasedNatIso.toNatIso (Bicategory.PseudoComma.cellIso f).symm) := sorry

/-- A pseudo-comma relative-inertia map applies the left endpoint map to the underlying
relative-inertia object. -/
@[simp, stacks 04Z4 "relative inertia action object readout"]
theorem map.obj (f : S ⟶ T) (A : (relativeInertia S.hom).obj) :
    ((map f).toFunctor.obj A).obj =
      (Bicategory.PseudoComma.left f).toFunctor.obj A.obj := sorry

/-- A pseudo-comma relative-inertia map applies the left endpoint map to the chosen
automorphism. -/
@[simp, stacks 04Z4 "relative inertia action automorphism readout"]
theorem map.aut (f : S ⟶ T) (A : (relativeInertia S.hom).obj) :
    ((map f).toFunctor.obj A).aut =
      (Bicategory.PseudoComma.left f).toFunctor.mapIso A.aut := sorry

/-- A pseudo-comma relative-inertia map applies the left endpoint map to the arrow underlying
each relative-inertia morphism. -/
@[simp, stacks 04Z4 "relative inertia action arrow readout"]
theorem map.hom (f : S ⟶ T) {A B : (relativeInertia S.hom).obj} (φ : A ⟶ B) :
    CategoryTheory.RelativeInertia.hom ((map f).toFunctor.map φ) =
      (Bicategory.PseudoComma.left f).toFunctor.map
        (CategoryTheory.RelativeInertia.hom φ) := sorry

end

end pseudoComma
end RelativeInertia
end BasedCategory
end CategoryTheory
