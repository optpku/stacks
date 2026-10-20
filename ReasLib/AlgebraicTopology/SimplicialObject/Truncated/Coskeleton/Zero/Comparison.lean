module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.KanExtension.Pointwise
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Coskeleton.Zero
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Zero
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 0182

# Comparison of explicit and canonical zero coskeletons

The explicit finite-self-product model and the right-Kan-extension zero coskeleton represent the
same degree-zero evaluation functor.  Their objectwise comparison only assumes the required powers
of the coefficient object and the existence of its chosen coskeleton.  Under uniform existence
hypotheses, this file also compares the corresponding functors by uniqueness of right adjoints.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial SimplexCategory.Truncated

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject.ZeroCoskeleton

variable {C : Type u} [Category.{v} C]

namespace canonical

section Objectwise

variable (X : C)
variable [((SimplicialObject.Truncated.constZero (C := C)).obj X).HasCoskeleton]

/-- Maps into the chosen coskeleton of the constant zero-truncated object on `X` are equivalent
to maps from degree zero into `X`. -/
@[stacks 0182 "objectwise canonical zero-coskeleton Hom equivalence"]
noncomputable def homEquiv (V : SimplicialObject C) :
    (V ⟶ ((SimplicialObject.Truncated.constZero (C := C)).obj X).coskeleton) ≃
      (V _⦋0⦌ ⟶ X) :=
  (SimplicialObject.Truncated.coskeleton.homEquiv
      ((SimplicialObject.Truncated.constZero (C := C)).obj X) V).trans
    (SimplicialObject.Truncated.zeroEquivalence
      (C := C)).fullyFaithfulFunctor.homEquiv

/-- The canonical zero-coskeleton classifier restricts a map, composes with the chosen
coskeleton counit, and then evaluates the resulting zero-truncated morphism. -/
@[simp, stacks 0182 "canonical zero-coskeleton Hom equivalence application"]
theorem homEquiv.apply (V : SimplicialObject C)
    (f : V ⟶ ((SimplicialObject.Truncated.constZero (C := C)).obj X).coskeleton) :
    homEquiv X V f =
      (SimplicialObject.Truncated.zeroEquivalence
        (C := C)).fullyFaithfulFunctor.homEquiv
        ((SimplexCategory.Truncated.inclusion 0).op.whiskerLeft f ≫
          SimplicialObject.Truncated.coskeleton.counit
            ((SimplicialObject.Truncated.constZero (C := C)).obj X)) := sorry

/-- The inverse canonical zero-coskeleton classifier first bundles the degree-zero map as a
zero-truncated morphism and then takes its universal coskeleton lift. -/
@[simp, stacks 0182 "canonical zero-coskeleton Hom equivalence inverse application"]
theorem homEquiv.symm_apply (V : SimplicialObject C) (f : V _⦋0⦌ ⟶ X) :
    (homEquiv X V).symm f =
      SimplicialObject.Truncated.coskeleton.lift
        ((SimplicialObject.Truncated.constZero (C := C)).obj X) V
        ((SimplicialObject.Truncated.zeroEquivalence
          (C := C)).fullyFaithfulFunctor.homEquiv.symm f) := sorry

/-- The objectwise canonical zero-coskeleton Hom equivalence is natural by precomposition in the
simplicial source. -/
@[stacks 0182 "objectwise canonical zero-coskeleton Hom equivalence source naturality"]
theorem homEquiv.precomp {V W : SimplicialObject C} (a : W ⟶ V)
    (f : V ⟶ ((SimplicialObject.Truncated.constZero (C := C)).obj X).coskeleton) :
    homEquiv X W (a ≫ f) = a.app (op ⦋0⦌) ≫ homEquiv X V f := sorry

/-- The chosen coskeleton of the constant zero-truncated object on `X` represents maps from
degree zero into `X`.  This owner requires only the singular coskeleton instance for `X`. -/
@[stacks 0182 "chosen zero coskeleton represents degree-zero maps"]
noncomputable def representableBy :
    (((SimplicialObject.evalZero (C := C)).op ⋙ yoneda.obj X).RepresentableBy
      ((SimplicialObject.Truncated.constZero (C := C)).obj X).coskeleton) where
  homEquiv {V} := homEquiv X V
  homEquiv_comp := homEquiv.precomp X

end Objectwise

section Functorial

variable [SimplicialObject.Truncated.HasCoskeletons C 0]

/-- The canonical zero-coskeleton functor on coefficient objects: first form the constant
zero-truncated object, then take its right Kan extension. -/
@[stacks 0182 "canonical zero-coskeleton functor on coefficient objects"]
noncomputable abbrev functor : C ⥤ SimplicialObject C :=
  SimplicialObject.Truncated.constZero (C := C) ⋙
    SimplicialObject.Truncated.cosk 0

/-- Degree-zero evaluation is left adjoint to the canonical zero-coskeleton functor on coefficient
objects. -/
@[stacks 0182 "canonical degree-zero coskeleton adjunction"]
noncomputable def adj : SimplicialObject.evalZero (C := C) ⊣ functor (C := C) :=
  ((SimplicialObject.coskAdj (C := C) 0).comp
      (SimplicialObject.Truncated.zeroEquivalence (C := C)).toAdjunction).ofNatIsoLeft
    (SimplicialObject.Truncated.evalZero.truncationIso (C := C))

end Functorial

end canonical

namespace selfProduct

section Objectwise

variable (X : C) [HasPositivePowers X]
variable [((SimplicialObject.Truncated.constZero (C := C)).obj X).HasCoskeleton]

/-- The objectwise canonical comparison from the explicit self-product model to the chosen right
Kan extension zero coskeleton. -/
@[stacks 0182 "objectwise comparison of explicit and canonical zero coskeletons"]
noncomputable def coskIso :
    ZeroCoskeleton.selfProduct X ≅
      ((SimplicialObject.Truncated.constZero (C := C)).obj X).coskeleton :=
  (ZeroCoskeleton.representableBy X).uniqueUpToIso (canonical.representableBy X)

/-- The forward objectwise comparison carries the explicit universal element to the canonical
universal element. -/
@[simp, stacks 0182 "forward objectwise zero-coskeleton universal element"]
theorem coskIso.hom_apply :
    canonical.homEquiv X (ZeroCoskeleton.selfProduct X) (coskIso X).hom =
      ZeroCoskeleton.homEquiv X (ZeroCoskeleton.selfProduct X)
        (𝟙 (ZeroCoskeleton.selfProduct X)) := sorry

/-- The inverse objectwise comparison carries the canonical universal element back to the
explicit universal element. -/
@[simp, stacks 0182 "inverse objectwise zero-coskeleton universal element"]
theorem coskIso.inv_apply :
    ZeroCoskeleton.homEquiv X
        ((SimplicialObject.Truncated.constZero (C := C)).obj X).coskeleton
        (coskIso X).inv =
      canonical.homEquiv X
        ((SimplicialObject.Truncated.constZero (C := C)).obj X).coskeleton
        (𝟙 ((SimplicialObject.Truncated.constZero (C := C)).obj X).coskeleton) := sorry

end Objectwise

section Functorial

variable [∀ X : C, HasPositivePowers X]
variable [SimplicialObject.Truncated.HasCoskeletons C 0]

/-- The explicit self-product zero coskeleton and the canonical right-Kan-extension zero
coskeleton are naturally isomorphic as functors of the coefficient object. -/
@[stacks 0182 "comparison of explicit and canonical zero coskeleton functors"]
noncomputable def functorIso :
    selfProduct.functor (C := C) ≅ canonical.functor (C := C) :=
  (selfProduct.adj (C := C)).rightAdjointUniq (canonical.adj (C := C))

/-- The component of the functorial zero-coskeleton comparison is the singular comparison
obtained from the two representing objects. -/
@[simp, stacks 0182 "zero-coskeleton functor comparison component"]
theorem functorIso_app (X : C) :
    (functorIso (C := C)).app X = coskIso X := sorry

/-- The forward objectwise zero-coskeleton comparison is the corresponding component of the
functor-level comparison under the uniform existence hypotheses. -/
@[simp, stacks 0182 "forward objectwise zero-coskeleton comparison"]
theorem coskIso_hom (X : C) :
    (coskIso X).hom = (functorIso (C := C)).hom.app X := sorry

/-- The inverse objectwise zero-coskeleton comparison is the corresponding component of the
functor-level comparison under the uniform existence hypotheses. -/
@[simp, stacks 0182 "inverse objectwise zero-coskeleton comparison"]
theorem coskIso_inv (X : C) :
    (coskIso X).inv = (functorIso (C := C)).inv.app X := sorry

/-- The forward comparison intertwines the canonical and explicit adjunction counits. -/
@[reassoc (attr := simp), stacks 0182 "forward zero-coskeleton comparison counit formula"]
theorem functorIso.hom_app_counit (X : C) :
    (SimplicialObject.evalZero (C := C)).map
          ((functorIso (C := C)).hom.app X) ≫
        (canonical.adj (C := C)).counit.app X =
      (selfProduct.adj (C := C)).counit.app X := sorry

/-- The inverse comparison intertwines the explicit and canonical adjunction counits. -/
@[reassoc (attr := simp), stacks 0182 "inverse zero-coskeleton comparison counit formula"]
theorem functorIso.inv_app_counit (X : C) :
    (SimplicialObject.evalZero (C := C)).map
          ((functorIso (C := C)).inv.app X) ≫
        (selfProduct.adj (C := C)).counit.app X =
      (canonical.adj (C := C)).counit.app X := sorry

/-- Transporting an explicit self-product map across the comparison agrees with the canonical
coskeleton adjunction Hom equivalence. -/
@[simp, stacks 0182 "forward zero-coskeleton comparison Hom formula"]
theorem canonicalHomEquiv {V : SimplicialObject C} {X : C}
    (f : V ⟶ ZeroCoskeleton.selfProduct X) :
    (canonical.adj (C := C)).homEquiv V X
        (ZeroCoskeleton.homEquiv X V f) =
      f ≫ (functorIso (C := C)).hom.app X := sorry

/-- Transporting a canonical zero-coskeleton map back to the explicit model agrees with the
explicit degree-zero Hom equivalence. -/
@[simp, stacks 0182 "inverse zero-coskeleton comparison Hom formula"]
theorem homEquiv_canonical {V : SimplicialObject C} {X : C}
    (f : V ⟶ (canonical.functor (C := C)).obj X) :
    ZeroCoskeleton.homEquiv X V
        (f ≫ (functorIso (C := C)).inv.app X) =
      ((canonical.adj (C := C)).homEquiv V X).symm f := sorry

end Functorial

end selfProduct

end CategoryTheory.SimplicialObject.ZeroCoskeleton
