module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Relative.ToInertia.Construction

import Mathlib.Tactic.CrossRefAttribute

/-!
# Computations for relative-to-absolute inertia on pseudo-comma arrows

This leaf exposes the underlying arrows of the canonical forward and inverse comparison
components without importing the pseudo-comma `2`-cell compatibility API.
-/

@[expose] public section

universe u v u₁ v₁

namespace CategoryTheory
namespace BasedCategory

open BasedCategory BasedFunctor BasedNatIso BasedNatTrans

variable {C : Type u} [Category.{v} C]

namespace RelativeInertia
namespace pseudoComma

variable
    {S T : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))}

noncomputable section

namespace toInertiaIso

/-- The forward pseudo-comma relative-to-absolute comparison component is the canonical neutral
objectwise comparison for its endpoint square. -/
@[simp, stacks 04Z5 "relative-to-absolute inertia forward comparison component"]
theorem hom.app (f : S ⟶ T) (A : (relativeInertia S.hom).obj) :
    (toInertiaIso f).hom.toNatTrans.app A =
      (RelativeInertia.toInertia.naturalityIso.component
        (Bicategory.PseudoComma.left f) (Bicategory.PseudoComma.right f)
        (Bicategory.PseudoComma.cellIso f).symm A).hom := sorry

/-- The inverse pseudo-comma relative-to-absolute comparison component is the reverse canonical
neutral objectwise comparison for its endpoint square. -/
@[simp, stacks 04Z5 "relative-to-absolute inertia inverse comparison component"]
theorem inv.app (f : S ⟶ T) (A : (relativeInertia S.hom).obj) :
    (toInertiaIso f).inv.toNatTrans.app A =
      (RelativeInertia.toInertia.naturalityIso.component
        (Bicategory.PseudoComma.left f) (Bicategory.PseudoComma.right f)
        (Bicategory.PseudoComma.cellIso f).symm A).inv := sorry

/-- Every forward pseudo-comma relative-to-absolute comparison component is vertical over the
unchanged base object. -/
@[stacks 04Z5 "relative-to-absolute inertia forward comparison verticality"]
theorem hom.app.isHomLift (f : S ⟶ T) (A : (relativeInertia S.hom).obj) :
    (inertia (Bicategory.ColaxComma.left T)).p.IsHomLift
      (𝟙 ((relativeInertia S.hom).p.obj A))
      ((toInertiaIso f).hom.toNatTrans.app A) := sorry

/-- Every inverse pseudo-comma relative-to-absolute comparison component is vertical over the
unchanged base object. -/
@[stacks 04Z5 "relative-to-absolute inertia inverse comparison verticality"]
theorem inv.app.isHomLift (f : S ⟶ T) (A : (relativeInertia S.hom).obj) :
    (inertia (Bicategory.ColaxComma.left T)).p.IsHomLift
      (𝟙 ((relativeInertia S.hom).p.obj A))
      ((toInertiaIso f).inv.toNatTrans.app A) := sorry

/-- The arrow underlying a forward pseudo-comma relative-to-absolute comparison component is
an identity on the image under the left endpoint. -/
@[simp, stacks 04Z5 "relative-to-absolute inertia forward underlying arrow"]
theorem hom.app.underlying (f : S ⟶ T) (A : (relativeInertia S.hom).obj) :
    CategoryTheory.RelativeInertia.hom
        ((toInertiaIso f).hom.toNatTrans.app A) =
      𝟙 ((Bicategory.PseudoComma.left f).toFunctor.obj A.obj) := sorry

/-- The arrow underlying an inverse pseudo-comma relative-to-absolute comparison component is
an identity on the image under the left endpoint. -/
@[simp, stacks 04Z5 "relative-to-absolute inertia inverse underlying arrow"]
theorem inv.app.underlying (f : S ⟶ T) (A : (relativeInertia S.hom).obj) :
    CategoryTheory.RelativeInertia.hom
        ((toInertiaIso f).inv.toNatTrans.app A) =
      𝟙 ((Bicategory.PseudoComma.left f).toFunctor.obj A.obj) := sorry

end toInertiaIso

end

end pseudoComma
end RelativeInertia
end BasedCategory
end CategoryTheory
