/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Relative.StrongTrans.Forget.Construction

import Mathlib.Tactic.CrossRefAttribute

/-!
# Computations for the pseudo-comma relative-inertia forgetful transformation
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory
namespace BasedCategory

open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

noncomputable section

namespace RelativeInertia
namespace pseudoComma

variable
    {S T : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))}

namespace forget.naturalityIso

/-- The forward arrow of the forgetful objectwise comparison is the identity. -/
@[simp, stacks 042H "relative-inertia forgetful forward component"]
theorem component.hom (f : S ⟶ T) (A : ((pseudofunctor C).obj S).obj) :
    (component f A).hom = 𝟙 _ := sorry

/-- The inverse arrow of the forgetful objectwise comparison is the identity. -/
@[simp, stacks 042H "relative-inertia forgetful inverse component"]
theorem component.inv (f : S ⟶ T) (A : ((pseudofunctor C).obj S).obj) :
    (component f A).inv = 𝟙 _ := sorry

/-- The forward component of relative-inertia forgetting is the supplied identity comparison. -/
@[simp, stacks 042H "relative-inertia forgetful packaged forward component"]
theorem hom.app (f : S ⟶ T) (A : ((pseudofunctor C).obj S).obj) :
    (forget.naturalityIso f).hom.toNatTrans.app A =
      (component f A).hom := sorry

/-- The inverse component of relative-inertia forgetting is the supplied identity comparison. -/
@[simp, stacks 042H "relative-inertia forgetful packaged inverse component"]
theorem inv.app (f : S ⟶ T) (A : ((pseudofunctor C).obj S).obj) :
    (forget.naturalityIso f).inv.toNatTrans.app A =
      (component f A).inv := sorry

end forget.naturalityIso

namespace forget.strongTrans

/-- The component of the relative-inertia forgetful transformation is the based forgetful map. -/
@[simp, stacks 042H "relative-inertia forgetful strong transformation component"]
theorem app
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))) :
    (forget.strongTrans C).app S = RelativeInertia.forget S.hom := sorry

/-- The naturality cell of the relative-inertia forgetful transformation is canonical. -/
@[simp, stacks 042H "relative-inertia forgetful strong transformation naturality"]
theorem naturality (f : S ⟶ T) :
    (forget.strongTrans C).naturality f = forget.naturalityIso f := sorry

end forget.strongTrans

end pseudoComma
end RelativeInertia

end

end BasedCategory
end CategoryTheory
