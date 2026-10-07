module

public import ReasLib.Algebra.Category.DifferentialGraded.Representable.Functor
public import ReasLib.Algebra.Category.DifferentialGraded.Functor.Triangulated
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Forget
public import ReasLib.CategoryTheory.Functor.Derived.Total.Triangulated

/-!
# Derived enriched representable functors

For an object `x` in an `R`-linear differential graded category, this file derives the
homotopy-level functor `Hom(x, -)` with values in right modules over `End(x)`.  Definedness may
be checked after forgetting the endomorphism action, while the resulting total right-derived
functor retains the enriched target.
-/

@[expose] public section

noncomputable section

universe u v w z t

open CategoryTheory
open scoped DifferentialGradedCategory

namespace DifferentialGradedCategory.Representable

variable {R : Type u} [CommRing R]
variable {C : Type v} [DifferentialGradedCategory.{u, v, w} R C]

/-- The homotopy-level enriched representable functor followed by the canonical localization
of right DG modules over `endomorphismDGA x`. -/
abbrev sourceFunctor (x : C) :
    K R C ⥤
      DifferentialGradedModule.Derived.Category.{u, w} (endomorphismDGA x) :=
  (representableDgFunctor x).mapK ⋙
    DifferentialGradedModule.Derived.Q (endomorphismDGA x)

/-- The ordinary derived-complex-valued functor underlying the enriched representable source. -/
abbrev underlyingSourceFunctor (x : C) :
    K R C ⥤ DerivedCategory (ModuleCat.{w} R) :=
  sourceFunctor x ⋙
    DifferentialGradedModule.Derived.forget (endomorphismDGA x)

/-- The underlying representable source factors through forgetting the DG-module action before
ordinary derived localization. -/
noncomputable def underlyingSourceFunctorFactors (x : C) :
    underlyingSourceFunctor x ≅
      (representableDgFunctor x).mapK ⋙
        (DifferentialGradedModule.Homotopy.forget (endomorphismDGA x) ⋙
          DerivedCategory.Qh (C := ModuleCat.{w} R)) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (representableDgFunctor x).mapK
      (DifferentialGradedModule.Derived.forgetFactors (endomorphismDGA x))

/-- The usual derived representable functor is source-defined everywhere after forgetting the
endomorphism-DGA action. -/
abbrev HasUnderlyingDerivedFunctor (x : C) (S : MorphismProperty (K R C)) : Prop :=
  Functor.RightDerived.EverywhereDefined (underlyingSourceFunctor x) S

/-- The enriched representable functor is source-defined everywhere with values in derived
right modules over `endomorphismDGA x`. -/
abbrev HasDerivedFunctor (x : C) (S : MorphismProperty (K R C)) : Prop :=
  Functor.RightDerived.EverywhereDefined (sourceFunctor x) S

variable {E : Type z} [Category.{t} E]

/-- Lemma 22.32.1 (09LK): the total right-derived enriched representable functor along a
localization `L`. -/
@[stacks 09LK "derived enriched representable functor"]
noncomputable def derivedFunctor
    (x : C) (L : K R C ⥤ E) (S : MorphismProperty (K R C))
    [L.IsLocalization S] [HasDerivedFunctor x S] :
    E ⥤ DifferentialGradedModule.Derived.Category.{u, w} (endomorphismDGA x) :=
  (sourceFunctor x).totalRightDerived L S

/-- The total derived representable functor is additive on the localized category. -/
@[stacks 09LK "additivity of the derived representable functor"]
noncomputable instance derivedFunctor_additive
    (x : C) (L : K R C ⥤ E) (S : MorphismProperty (K R C))
    [Preadditive E] [L.IsLocalization S] [HasDerivedFunctor x S] :
    (derivedFunctor x L S).Additive := sorry

/-- The total derived representable functor is linear over the ground ring. -/
@[stacks 09LK "linearity of the derived representable functor"]
noncomputable instance derivedFunctor_linear
    (x : C) (L : K R C ⥤ E) (S : MorphismProperty (K R C))
    [Preadditive E] [Linear R E] [L.IsLocalization S] [HasDerivedFunctor x S] :
    (derivedFunctor x L S).Linear R := sorry

/-- The canonical comparison from enriched representable Hom on the homotopy category to its
total right-derived functor. -/
noncomputable def derivedUnit
    (x : C) (L : K R C ⥤ E) (S : MorphismProperty (K R C))
    [L.IsLocalization S] [HasDerivedFunctor x S] :
    sourceFunctor x ⟶ L ⋙ derivedFunctor x L S :=
  (sourceFunctor x).totalRightDerivedUnit L S

/-- The derived enriched representable functor and its canonical unit satisfy the right-derived
universal property. -/
instance derivedFunctor_isRightDerived
    (x : C) (L : K R C ⥤ E) (S : MorphismProperty (K R C))
    [L.IsLocalization S] [HasDerivedFunctor x S] :
    (derivedFunctor x L S).IsRightDerivedFunctor (derivedUnit x L S) S := sorry

/-- The comparison unit obtained by forgetting the endomorphism-DGA action on the derived
enriched representable functor. -/
noncomputable def derivedForgetUnit
    (x : C) (L : K R C ⥤ E) (S : MorphismProperty (K R C))
    [L.IsLocalization S] [HasUnderlyingDerivedFunctor x S] :
    underlyingSourceFunctor x ⟶
      L ⋙ (derivedFunctor x L S ⋙
        DifferentialGradedModule.Derived.forget (endomorphismDGA x)) :=
  Functor.whiskerRight (derivedUnit x L S)
      (DifferentialGradedModule.Derived.forget (endomorphismDGA x)) ≫
    (Functor.associator L (derivedFunctor x L S)
      (DifferentialGradedModule.Derived.forget (endomorphismDGA x))).hom

/-- Forgetting the endomorphism-DGA action preserves the right-derived universal property of
the enriched representable functor. -/
instance derivedForget_isRightDerived
    (x : C) (L : (K R C) ⥤ E) (S : MorphismProperty (K R C))
    [L.IsLocalization S] [HasUnderlyingDerivedFunctor x S] :
    (derivedFunctor x L S ⋙
      DifferentialGradedModule.Derived.forget (endomorphismDGA x)).IsRightDerivedFunctor
        (derivedForgetUnit x L S) S := sorry

/-- Lemma 22.32.1 (09LK): after forgetting the endomorphism-DGA action, the derived enriched
representable functor is canonically isomorphic to the ordinary derived representable functor. -/
@[stacks 09LK "underlying derived representable comparison"]
noncomputable def derivedForgetIso
    (x : C) (L : (K R C) ⥤ E) (S : MorphismProperty (K R C))
    [L.IsLocalization S] [HasUnderlyingDerivedFunctor x S] :
    derivedFunctor x L S ⋙
        DifferentialGradedModule.Derived.forget (endomorphismDGA x) ≅
      (underlyingSourceFunctor x).totalRightDerived L S :=
  Functor.rightDerivedUnique
    (derivedFunctor x L S ⋙
      DifferentialGradedModule.Derived.forget (endomorphismDGA x))
    ((underlyingSourceFunctor x).totalRightDerived L S)
    (derivedForgetUnit x L S)
    ((underlyingSourceFunctor x).totalRightDerivedUnit L S) S

section

variable (x : C) (S : MorphismProperty (K R C))
variable [HasUnderlyingDerivedFunctor x S]

/- The ordinary underlying derived-Hom hypothesis automatically supplies enriched
everywhere-definedness; no local instance is required by downstream users. -/
#synth HasDerivedFunctor x S

end

end DifferentialGradedCategory.Representable
