module

public import Mathlib.CategoryTheory.Adjunction.Reflective
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.Scheme.Reduction.Functor

/-!
# Reduced schemes as a coreflective subcategory

The canonical reducedness instance on a full-subcategory object is global in
this namespace, so the universal property does not reconstruct it locally.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The full subcategory of reduced schemes. -/
@[stacks 0356 "reduced-scheme full subcategory"]
abbrev Reduced : Type (u + 1) :=
  ObjectProperty.FullSubcategory (IsReduced : ObjectProperty Scheme.{u})

namespace Reduced

/-- A reduced-scheme object carries its defining reducedness property as a canonical instance. -/
@[stacks 0356, instance]
instance instIsReducedObj (X : Reduced.{u}) : IsReduced X.obj := sorry

/-- The inclusion of reduced schemes into schemes. -/
@[stacks 0356 "reduced-scheme inclusion"]
abbrev ι : Reduced.{u} ⥤ Scheme.{u} :=
  ObjectProperty.ι (IsReduced : ObjectProperty Scheme.{u})

/-- Every object of the reduction functor is reduced. -/
@[stacks 0356 "reducedness of scheme-theoretic reduction"]
theorem reductionFunctor_obj_isReduced (X : Scheme.{u}) :
    IsReduced (reductionFunctor.obj X) := sorry

/-- Reduction regarded as a functor to the full subcategory of reduced schemes. -/
@[stacks 0356 "reduction coreflector"]
noncomputable def coreflector : Scheme.{u} ⥤ Reduced.{u} :=
  ObjectProperty.lift (IsReduced : ObjectProperty Scheme.{u}) reductionFunctor
    reductionFunctor_obj_isReduced

/-- The coreflector acts on objects by scheme-theoretic reduction. -/
@[simp, stacks 0356 "reduction coreflector object"]
theorem coreflector_obj (X : Scheme.{u}) :
    (coreflector.obj X).obj = reduction X := sorry

/-- The underlying morphism of a coreflector map is the canonical map on reductions. -/
@[simp, stacks 0356 "reduction coreflector map"]
theorem coreflector_map {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (coreflector.map f).hom = reductionMap f := sorry

/-- Left inverse law for the reduced-scheme coreflection hom equivalence. -/
@[stacks 0356 "reduction coreflection left inverse"]
theorem homEquiv_left_inv (X : Reduced.{u}) (Y : Scheme.{u})
    (f : ι.obj X ⟶ Y) :
    (ObjectProperty.homMk (Hom.reductionLift f) : X ⟶ coreflector.obj Y).hom ≫
      reductionι Y = f := sorry

/-- Right inverse law for the reduced-scheme coreflection hom equivalence. -/
@[stacks 0356 "reduction coreflection right inverse"]
theorem homEquiv_right_inv (X : Reduced.{u}) (Y : Scheme.{u})
    (g : X ⟶ coreflector.obj Y) :
    (ObjectProperty.homMk (Hom.reductionLift (g.hom ≫ reductionι Y)) :
      X ⟶ coreflector.obj Y) = g := sorry

/-- The universal property of reduction in the full subcategory of reduced schemes. -/
@[stacks 0356 "reduction coreflection hom equivalence"]
noncomputable def homEquiv (X : Reduced.{u}) (Y : Scheme.{u}) :
    (ι.obj X ⟶ Y) ≃ (X ⟶ coreflector.obj Y) where
  toFun f := ObjectProperty.homMk (Hom.reductionLift f)
  invFun g := g.hom ≫ reductionι Y
  left_inv := homEquiv_left_inv X Y
  right_inv := homEquiv_right_inv X Y

/-- Naturality on the reduced-scheme variable for the coreflection hom equivalence. -/
@[stacks 0356 "reduction coreflection left naturality"]
theorem homEquiv_naturality_left_symm
    {X' X : Reduced.{u}} {Y : Scheme.{u}} (f : X' ⟶ X)
    (g : X ⟶ coreflector.obj Y) :
    (homEquiv X' Y).symm (f ≫ g) =
      ι.map f ≫ (homEquiv X Y).symm g := sorry

/-- Naturality on the scheme variable for the coreflection hom equivalence. -/
@[stacks 0356 "reduction coreflection right naturality"]
theorem homEquiv_naturality_right
    {X : Reduced.{u}} {Y Y' : Scheme.{u}} (f : ι.obj X ⟶ Y) (g : Y ⟶ Y') :
    homEquiv X Y' (f ≫ g) = homEquiv X Y f ≫ coreflector.map g := sorry

/-- The inclusion of reduced schemes is left adjoint to reduction. -/
@[stacks 0356 "reduction coreflection"]
noncomputable def adjunction : ι.{u} ⊣ coreflector.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv
      homEquiv_naturality_left_symm := homEquiv_naturality_left_symm
      homEquiv_naturality_right := homEquiv_naturality_right }

/-- Reduced schemes form a coreflective full subcategory of schemes. -/
@[stacks 0356, instance]
noncomputable instance instCoreflective : Coreflective ι.{u} where
  R := coreflector
  adj := adjunction

/-- Viewing the coreflector in schemes recovers the reduction functor. -/
@[stacks 0356 "reduction coreflector comparison"]
noncomputable def coreflectorCompιIso : coreflector ⋙ ι ≅ reductionFunctor :=
  Iso.refl _

/-- The counit of the reduction coreflection is the reduction inclusion. -/
@[simp, stacks 0356 "reduction coreflection counit"]
theorem adjunction_counit_app (Y : Scheme.{u}) :
    adjunction.counit.app Y = reductionι Y := sorry

/-- The reduction-inclusion natural transformation is the coreflection counit. -/
@[simp, stacks 0356 "reduction inclusion is coreflection counit"]
theorem reductionιNatTrans_eq_adjunction_counit :
    reductionιNatTrans = adjunction.counit := sorry

end Reduced

end AlgebraicGeometry.Scheme
