module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Relative.Pseudofunctor.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Section.Construction
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

import Mathlib.Tactic.CrossRefAttribute

/-!
# Component and naturality data for the pseudo-comma identity section

This leaf owns the public objectwise comparison and its naturality/verticality data.  The
private coherence obligations needed to package these comparisons as a `StrongTrans` live in
`Construction.StrongTrans`.
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

/-- The identity arrow intertwines the neutral automorphisms in pseudo-comma identity-section
naturality. -/
@[stacks 04Z3 "relative-inertia identity-section component compatibility"]
theorem component.comm (f : S ⟶ T)
    (x : ((Bicategory.PseudoComma.fst
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))).obj S).obj) :
    (((Bicategory.PseudoComma.fst
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))).map f ≫
        RelativeInertia.identitySection T.hom).obj x).aut.hom ≫ 𝟙 _ =
      𝟙 _ ≫
        ((RelativeInertia.identitySection S.hom ≫
          (pseudofunctor C).map f).obj x).aut.hom := sorry

/-- The objectwise pseudo-comma identity-section comparison has identity underlying arrow. -/
@[stacks 04Z3 "relative-inertia identity-section component"]
def component (f : S ⟶ T)
    (x : ((Bicategory.PseudoComma.fst
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))).obj S).obj) :
    ((Bicategory.PseudoComma.fst
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))).map f ≫
        RelativeInertia.identitySection T.hom).obj x ≅
      (RelativeInertia.identitySection S.hom ≫
        (pseudofunctor C).map f).obj x :=
  CategoryTheory.RelativeInertia.isoMk T.hom.toFunctor (Iso.refl _)
    (component.comm f x)

/-- The explicit identity-section comparisons are natural in left-endpoint morphisms. -/
@[stacks 04Z3 "relative-inertia identity-section component naturality"]
theorem component.naturality (f : S ⟶ T)
    {x y : ((Bicategory.PseudoComma.fst
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))).obj S).obj}
    (g : x ⟶ y) :
    let L := ((Bicategory.PseudoComma.fst
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))).map f ≫
        RelativeInertia.identitySection T.hom).toFunctor
    let R := (RelativeInertia.identitySection S.hom ≫
      (pseudofunctor C).map f).toFunctor
    let e : ∀ z, L.obj z ≅ R.obj z := component f
    L.map g ≫ (e y).hom = (e x).hom ≫ R.map g := sorry

/-- The inverse pseudo-comma identity-section comparison components are natural in left-endpoint
morphisms. -/
@[reassoc, stacks 04Z3 "relative-inertia identity-section inverse component naturality"]
theorem component.invNaturality (f : S ⟶ T)
    {x y : ((Bicategory.PseudoComma.fst
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))).obj S).obj}
    (g : x ⟶ y) :
    let L := ((Bicategory.PseudoComma.fst
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))).map f ≫
        RelativeInertia.identitySection T.hom).toFunctor
    let R := (RelativeInertia.identitySection S.hom ≫
      (pseudofunctor C).map f).toFunctor
    let e : ∀ z, L.obj z ≅ R.obj z := component f
    (e x).inv ≫ L.map g = R.map g ≫ (e y).inv := sorry

/-- Every identity-section comparison is vertical over the pseudo-comma base. -/
@[stacks 04Z3 "relative-inertia identity-section component verticality"]
theorem component.isHomLift (f : S ⟶ T)
    (x : ((Bicategory.PseudoComma.fst
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))).obj S).obj) :
    ((pseudofunctor C).obj T).p.IsHomLift
      (𝟙 ((Bicategory.PseudoComma.fst
        (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
        (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))).obj S).p.obj x)
      (component f x).hom := sorry

/-- Every inverse pseudo-comma identity-section comparison component is vertical over the identity
base arrow. -/
@[stacks 04Z3 "relative-inertia identity-section inverse component verticality"]
theorem component.inv.isHomLift (f : S ⟶ T)
    (x : ((Bicategory.PseudoComma.fst
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))).obj S).obj) :
    ((pseudofunctor C).obj T).p.IsHomLift
      (𝟙 ((Bicategory.PseudoComma.fst
        (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
        (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))).obj S).p.obj x)
      (component f x).inv := sorry

end identitySection.naturalityIso

/-- The naturality isomorphism for the neutral section along a pseudo-comma square. -/
@[stacks 04Z3 "relative-inertia identity-section naturality isomorphism"]
def identitySection.naturalityIso (f : S ⟶ T) :
    (Bicategory.PseudoComma.fst
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))).map f ≫
        RelativeInertia.identitySection T.hom ≅
      RelativeInertia.identitySection S.hom ≫ (pseudofunctor C).map f :=
  BasedNatIso.ofComponents
    (identitySection.naturalityIso.component f)
    (identitySection.naturalityIso.component.naturality f)
    (identitySection.naturalityIso.component.isHomLift f)

end pseudoComma
end RelativeInertia

end

end BasedCategory
end CategoryTheory
