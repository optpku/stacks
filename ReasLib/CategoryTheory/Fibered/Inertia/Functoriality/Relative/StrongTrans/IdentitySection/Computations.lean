module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Relative.StrongTrans.IdentitySection.Construction

import Mathlib.Tactic.CrossRefAttribute

/-!
# Computations for the pseudo-comma relative-inertia identity section
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

namespace identitySection.naturalityIso

/-- The forward identity-section comparison has identity underlying ambient arrow. -/
@[simp, stacks 04Z3 "relative-inertia identity-section forward underlying arrow"]
theorem component.hom.underlying (f : S ⟶ T)
    (x : ((Bicategory.PseudoComma.fst
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))).obj S).obj) :
    CategoryTheory.RelativeInertia.hom (component f x).hom =
      𝟙 ((Bicategory.PseudoComma.left f).toFunctor.obj x) := sorry

/-- The inverse identity-section comparison has identity underlying ambient arrow. -/
@[simp, stacks 04Z3 "relative-inertia identity-section inverse underlying arrow"]
theorem component.inv.underlying (f : S ⟶ T)
    (x : ((Bicategory.PseudoComma.fst
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))).obj S).obj) :
    CategoryTheory.RelativeInertia.hom (component f x).inv =
      𝟙 ((Bicategory.PseudoComma.left f).toFunctor.obj x) := sorry

/-- The forward naturality component is the explicit relative-inertia comparison. -/
@[simp, stacks 04Z3 "relative-inertia identity-section packaged forward component"]
theorem hom.app (f : S ⟶ T)
    (x : ((Bicategory.PseudoComma.fst
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))).obj S).obj) :
    (identitySection.naturalityIso f).hom.toNatTrans.app x =
      (component f x).hom := sorry

/-- The inverse naturality component is the reverse explicit relative-inertia comparison. -/
@[simp, stacks 04Z3 "relative-inertia identity-section packaged inverse component"]
theorem inv.app (f : S ⟶ T)
    (x : ((Bicategory.PseudoComma.fst
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))).obj S).obj) :
    (identitySection.naturalityIso f).inv.toNatTrans.app x =
      (component f x).inv := sorry

/-- The forward naturality component has identity underlying ambient arrow. -/
@[simp, stacks 04Z3 "relative-inertia identity-section packaged forward underlying arrow"]
theorem hom.app.underlying (f : S ⟶ T)
    (x : ((Bicategory.PseudoComma.fst
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))).obj S).obj) :
    CategoryTheory.RelativeInertia.hom
        ((identitySection.naturalityIso f).hom.toNatTrans.app x) =
      𝟙 ((Bicategory.PseudoComma.left f).toFunctor.obj x) := sorry

/-- The inverse naturality component has identity underlying ambient arrow. -/
@[simp, stacks 04Z3 "relative-inertia identity-section packaged inverse underlying arrow"]
theorem inv.app.underlying (f : S ⟶ T)
    (x : ((Bicategory.PseudoComma.fst
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))).obj S).obj) :
    CategoryTheory.RelativeInertia.hom
        ((identitySection.naturalityIso f).inv.toNatTrans.app x) =
      𝟙 ((Bicategory.PseudoComma.left f).toFunctor.obj x) := sorry

end identitySection.naturalityIso

namespace identitySection.strongTrans

/-- The component of the relative-inertia neutral-section transformation is the canonical
based identity section. -/
@[simp, stacks 04Z3 "relative-inertia identity-section strong transformation component"]
theorem app
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))) :
    (identitySection.strongTrans C).app S =
      RelativeInertia.identitySection S.hom := sorry

/-- The naturality cell of the relative-inertia neutral section is canonical. -/
@[simp, stacks 04Z3 "relative-inertia identity-section strong transformation naturality"]
theorem naturality (f : S ⟶ T) :
    (identitySection.strongTrans C).naturality f =
      identitySection.naturalityIso f := sorry

end identitySection.strongTrans

end pseudoComma
end RelativeInertia

end

end BasedCategory
end CategoryTheory
