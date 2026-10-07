module

public import Mathlib.CategoryTheory.Adjunction.Reflective
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.Scheme.Reduction.Over

/-!
# Reduced schemes over a base as a coreflective subcategory
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Over

/-- The full subcategory of schemes over `S` whose underlying scheme is reduced. -/
@[stacks 0356 "relative reduced-scheme full subcategory"]
abbrev Reduced (S : Scheme.{u}) : Type (u + 1) :=
  ObjectProperty.FullSubcategory
    (fun X : CategoryTheory.Over S ↦ IsReduced X.left)

namespace Reduced

/-- An object of the reduced over-category carries its reducedness as a canonical instance. -/
@[stacks 0356, instance]
instance instIsReducedObj (S : Scheme.{u}) (X : Reduced S) : IsReduced X.obj.left := sorry

/-- The inclusion of reduced schemes over `S`. -/
@[stacks 0356 "relative reduced-scheme inclusion"]
abbrev ι (S : Scheme.{u}) : Reduced S ⥤ CategoryTheory.Over S :=
  ObjectProperty.ι (fun X : CategoryTheory.Over S ↦ IsReduced X.left)

/-- Every object of the relative reduction functor is reduced. -/
@[stacks 0356 "reducedness of relative scheme-theoretic reduction"]
theorem reductionFunctor_obj_isReduced
    (S : Scheme.{u}) (X : CategoryTheory.Over S) :
    IsReduced ((reductionFunctor S).obj X).left := sorry

/-- Relative reduction as a functor to reduced schemes over `S`. -/
@[stacks 0356 "relative reduction coreflector"]
noncomputable def coreflector (S : Scheme.{u}) :
    CategoryTheory.Over S ⥤ Reduced S :=
  ObjectProperty.lift (fun X : CategoryTheory.Over S ↦ IsReduced X.left)
    (reductionFunctor S) (reductionFunctor_obj_isReduced S)

/-- The relative coreflector acts on objects by relative reduction. -/
@[simp, stacks 0356 "relative reduction coreflector object"]
theorem coreflector_obj
    (S : Scheme.{u}) (X : CategoryTheory.Over S) :
    ((coreflector S).obj X).obj = reduction X := sorry

/-- The underlying morphism of a relative coreflector map is `reductionMap`. -/
@[simp, stacks 0356 "relative reduction coreflector map"]
theorem coreflector_map
    (S : Scheme.{u}) {X Y : CategoryTheory.Over S} (f : X ⟶ Y) :
    ((coreflector S).map f).hom = reductionMap f := sorry

/-- Left inverse law for the relative coreflection hom equivalence. -/
@[stacks 0356 "relative reduction coreflection left inverse"]
theorem homEquiv_left_inv
    (S : Scheme.{u}) (X : Reduced S) (Y : CategoryTheory.Over S)
    (f : (ι S).obj X ⟶ Y) :
    (ObjectProperty.homMk (Hom.reductionLift f) :
      X ⟶ (coreflector S).obj Y).hom ≫ reductionι Y = f := sorry

/-- Right inverse law for the relative coreflection hom equivalence. -/
@[stacks 0356 "relative reduction coreflection right inverse"]
theorem homEquiv_right_inv
    (S : Scheme.{u}) (X : Reduced S) (Y : CategoryTheory.Over S)
    (g : X ⟶ (coreflector S).obj Y) :
    (ObjectProperty.homMk (Hom.reductionLift (g.hom ≫ reductionι Y)) :
      X ⟶ (coreflector S).obj Y) = g := sorry

/-- The universal property of relative reduction in the reduced full subcategory. -/
@[stacks 0356 "relative reduction coreflection hom equivalence"]
noncomputable def homEquiv
    (S : Scheme.{u}) (X : Reduced S) (Y : CategoryTheory.Over S) :
    ((ι S).obj X ⟶ Y) ≃ (X ⟶ (coreflector S).obj Y) where
  toFun f := ObjectProperty.homMk (Hom.reductionLift f)
  invFun g := g.hom ≫ reductionι Y
  left_inv := homEquiv_left_inv S X Y
  right_inv := homEquiv_right_inv S X Y

/-- Naturality on the reduced source for the relative coreflection hom equivalence. -/
@[stacks 0356 "relative reduction coreflection left naturality"]
theorem homEquiv_naturality_left_symm
    (S : Scheme.{u}) {X' X : Reduced S} {Y : CategoryTheory.Over S}
    (f : X' ⟶ X) (g : X ⟶ (coreflector S).obj Y) :
    (homEquiv S X' Y).symm (f ≫ g) =
      (ι S).map f ≫ (homEquiv S X Y).symm g := sorry

/-- Naturality on the target for the relative coreflection hom equivalence. -/
@[stacks 0356 "relative reduction coreflection right naturality"]
theorem homEquiv_naturality_right
    (S : Scheme.{u}) {X : Reduced S} {Y Y' : CategoryTheory.Over S}
    (f : (ι S).obj X ⟶ Y) (g : Y ⟶ Y') :
    homEquiv S X Y' (f ≫ g) =
      homEquiv S X Y f ≫ (coreflector S).map g := sorry

/-- The inclusion of reduced schemes over `S` is left adjoint to relative reduction. -/
@[stacks 0356 "relative reduction coreflection"]
noncomputable def adjunction (S : Scheme.{u}) :
    ι S ⊣ coreflector S :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv S
      homEquiv_naturality_left_symm := homEquiv_naturality_left_symm S
      homEquiv_naturality_right := homEquiv_naturality_right S }

/-- Reduced schemes over `S` form a coreflective full subcategory. -/
@[stacks 0356, instance]
noncomputable instance instCoreflective (S : Scheme.{u}) : Coreflective (ι S) where
  R := coreflector S
  adj := adjunction S

/-- Forgetting the full-subcategory wrapper recovers the relative reduction functor. -/
@[stacks 0356 "relative reduction coreflector comparison"]
noncomputable def coreflectorCompιIso (S : Scheme.{u}) :
    coreflector S ⋙ ι S ≅ reductionFunctor S :=
  Iso.refl _

/-- The counit of relative reduction is the relative reduction inclusion. -/
@[simp, stacks 0356 "relative reduction coreflection counit"]
theorem adjunction_counit_app
    (S : Scheme.{u}) (Y : CategoryTheory.Over S) :
    (adjunction S).counit.app Y = reductionι Y := sorry

/-- The relative reduction-inclusion transformation is the coreflection counit. -/
@[simp, stacks 0356 "relative reduction inclusion is coreflection counit"]
theorem reductionιNatTrans_eq_adjunction_counit (S : Scheme.{u}) :
    reductionιNatTrans S = (adjunction S).counit := sorry

end Reduced

end AlgebraicGeometry.Over
