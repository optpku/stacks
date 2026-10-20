module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.TensorWithObject.Derived.Functor
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.RHom
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.FromModules
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyP.Localization
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.RHom

/-!
# Derived Hom before and after tensoring with a complex

For a complex `K` on a ringed site, this file owns the two abstract bifunctors occurring in the
derived tensor-Hom comparison:

* `Source.functor K` is derived Hom for right DG modules over `endDGA K`;
* `Target.functor K` applies derived tensor with `K` in both variables and then global derived
  Hom.

The reusable DG-module and Grothendieck-abelian owners supply both total-derived-functor
instances.  On property-(P) modules the comparison is the strict enriched-Hom map followed by
the global derived-Hom unit.  The property-(P) localization model then descends this map to
arbitrary derived objects.  This construction is deliberately not replaced by the different
operation of right-deriving `Hom(F(-), F(-))` in both variables.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory
open DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace SheafOfModules.RingedSite.TensorWithObject.Derived.Hom

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {O : Sheaf J CommRingCat.{max u v}}

namespace Source

/-- The `D(ℤ)`-valued derived Hom bifunctor of right DG modules over `endDGA K`. -/
@[stacks 0CS6 "source of the derived tensor-Hom comparison"]
noncomputable abbrev functor (K : Complex (J := J) (O := O)) :=
  DifferentialGradedModule.Derived.RHom.functor (endDGA.{u, v} K)

end Source

namespace Target

/-- Apply derived tensor with `K` in both variables and then take global derived Hom. -/
@[stacks 0CS6 "target of the derived tensor-Hom comparison"]
noncomputable abbrev functor (K : Complex (J := J) (O := O)) :=
  ((tensorFunctor K).op.prod (tensorFunctor K)) ⋙
    RingedSite.Hom.ModuleDerived.RHom.maxFunctor J O

end Target

namespace PropertyP

/-- Pairs of property-(P) homotopy objects on which the tensor-Hom comparison is computed. -/
@[stacks 0CS6 "property-P comparison domain"]
abbrev Domain (K : Complex (J := J) (O := O)) :=
  (DifferentialGradedModule.Homotopy.propertyP (endDGA.{u, v} K)).FullSubcategoryᵒᵖ ×
    (DifferentialGradedModule.Homotopy.propertyP (endDGA.{u, v} K)).FullSubcategory

/-- The simultaneous quasi-isomorphism system on pairs of property-(P) DG homotopy
objects. -/
@[stacks 0CS6 "property-P quasi-isomorphisms for the Hom comparison"]
abbrev qis (K : Complex (J := J) (O := O)) : MorphismProperty (Domain K) :=
  (DifferentialGradedModule.Homotopy.PropertyP.qis (endDGA.{u, v} K)).op.prod
    (DifferentialGradedModule.Homotopy.PropertyP.qis (endDGA.{u, v} K))

/-- The product localization from pairs of property-(P) objects to pairs of arbitrary derived
DG modules. -/
@[stacks 0CS6 "property-P product localization for the Hom comparison"]
noncomputable abbrev localization (K : Complex (J := J) (O := O)) :=
  (DifferentialGradedModule.Homotopy.PropertyP.localization (endDGA.{u, v} K)).op.prod
    (DifferentialGradedModule.Homotopy.PropertyP.localization (endDGA.{u, v} K))

/-- On property-(P) objects, strict enriched Hom maps to global derived Hom after tensoring,
transported from strict tensor values to derived tensor values. -/
@[stacks 0CS6 "property-P component of the derived tensor-Hom comparison"]
noncomputable def comparisonApp (K : Complex (J := J) (O := O))
    (M N : Modules K)
    (hM : DifferentialGradedModule.HasPropertyP (endDGA.{u, v} K) M)
    (hN : DifferentialGradedModule.HasPropertyP (endDGA.{u, v} K) N) :
    (Source.functor K).obj
        (Opposite.op ((DifferentialGradedModule.Derived.fromModules
          (endDGA.{u, v} K)).obj M),
          (DifferentialGradedModule.Derived.fromModules (endDGA.{u, v} K)).obj N) ⟶
      (Target.functor K).obj
        (Opposite.op ((DifferentialGradedModule.Derived.fromModules
          (endDGA.{u, v} K)).obj M),
          (DifferentialGradedModule.Derived.fromModules (endDGA.{u, v} K)).obj N) :=
  (DifferentialGradedModule.Derived.RHom.unitAppIsoOfPropertyP
      (endDGA.{u, v} K) M N hM).inv ≫
    (DifferentialGradedCategory.HomComplex.Derived.mapNatTrans
      (TensorWithObject.tensorFunctor K)).app
        (Opposite.op ((DifferentialGradedModule.toK (endDGA.{u, v} K)).obj M),
          (DifferentialGradedModule.toK (endDGA.{u, v} K)).obj N) ≫
    (RingedSite.Hom.ModuleDerived.RHom.maxUnit J O).app
        (Opposite.op ((TensorWithObject.tensorFunctor K).mapK.obj
            ((DifferentialGradedModule.toK (endDGA.{u, v} K)).obj M)),
          (TensorWithObject.tensorFunctor K).mapK.obj
            ((DifferentialGradedModule.toK (endDGA.{u, v} K)).obj N)) ≫
    (RingedSite.Hom.ModuleDerived.RHom.maxFunctor J O).map
        ((tensorCounitAppIso K M hM).hom.op,
          (tensorCounitAppIso K N hN).inv)

/-- The property-(P) component indexed by a pair of full-subcategory objects. -/
@[stacks 0CS6 "property-P comparison component"]
noncomputable abbrev component (K : Complex (J := J) (O := O)) (X : Domain K) :=
  comparisonApp K X.1.unop.obj.obj X.2.obj.obj X.1.unop.property X.2.property

/-- Naturality of the strict comparison on pairs of property-(P) DG homotopy models. -/
@[reassoc, stacks 0CS6 "naturality of the property-P Hom comparison"]
theorem comparison_naturality (K : Complex (J := J) (O := O))
    {X Y : Domain K} (f : X ⟶ Y) :
    (localization K ⋙ Source.functor K).map f ≫
        component K Y =
      component K X ≫
        (localization K ⋙ Target.functor K).map f := sorry

/-- The property-(P) components form a natural transformation on the full subcategory of good
DG homotopy models. -/
@[stacks 0CS6 "property-P derived tensor-Hom comparison"]
noncomputable def comparison (K : Complex (J := J) (O := O)) :
    localization K ⋙ Source.functor K ⟶ localization K ⋙ Target.functor K where
  app X := component K X
  naturality _ _ f := comparison_naturality K f

end PropertyP

/-- Lemma 22.35.4 (0CS6): the canonical morphism from derived Hom of DG modules to global
derived Hom after tensoring both variables with `K`. -/
@[stacks 0CS6 "derived tensor-Hom comparison"]
noncomputable def comparison (K : Complex (J := J) (O := O)) :
    Source.functor K ⟶ Target.functor K :=
  Localization.liftNatTrans (PropertyP.localization K) (PropertyP.qis K)
    (PropertyP.localization K ⋙ Source.functor K)
    (PropertyP.localization K ⋙ Target.functor K)
    (Source.functor K) (Target.functor K) (PropertyP.comparison K)

/-- Restricting the derived tensor-Hom comparison to property-(P) models recovers its strict
construction. -/
@[reassoc, stacks 0CS6 "property-P restriction of the derived tensor-Hom comparison"]
theorem comparison_fac (K : Complex (J := J) (O := O)) :
    Functor.whiskerLeft (PropertyP.localization K) (comparison K) =
      PropertyP.comparison K := sorry

/-- The derived tensor-Hom comparison evaluated on arbitrary derived DG modules. -/
@[stacks 0CS6 "derived tensor-Hom comparison on objects"]
noncomputable abbrev comparisonApp (K : Complex (J := J) (O := O))
    (M N : DifferentialGradedModule.Derived.Category (endDGA.{u, v} K)) :
    (Source.functor K).obj (Opposite.op M, N) ⟶
      (Target.functor K).obj (Opposite.op M, N) :=
  (comparison K).app (Opposite.op M, N)

/-- On property-(P) representatives, the abstract comparison is the explicit strict
enriched-Hom comparison. -/
@[stacks 0CS6 "property-P computation of the derived tensor-Hom comparison"]
theorem comparison_app_propertyP (K : Complex (J := J) (O := O))
    (M N : Modules K)
    (hM : DifferentialGradedModule.HasPropertyP (endDGA.{u, v} K) M)
    (hN : DifferentialGradedModule.HasPropertyP (endDGA.{u, v} K) N) :
    comparisonApp K
        ((DifferentialGradedModule.Derived.fromModules (endDGA.{u, v} K)).obj M)
        ((DifferentialGradedModule.Derived.fromModules (endDGA.{u, v} K)).obj N) =
      PropertyP.comparisonApp K M N hM hN := sorry

end SheafOfModules.RingedSite.TensorWithObject.Derived.Hom
