/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.CategoryHomology.Bar.Augmentation
public import ReasLib.CategoryTheory.Homology.HomologicalDeltaFunctor.ExactComplex
public import ReasLib.CategoryTheory.Homology.HomologicalDeltaFunctor.Coeffaceable
public import ReasLib.CategoryTheory.Homology.HomologicalDeltaFunctor.Universal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Homological delta functor of the bar construction

The explicit bar complex is the resolution-independent root for category homology.  This leaf
packages its coefficient functor as an exact chain-complex construction and exposes the resulting
homological delta functor before any derived-category comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w

namespace CategoryTheory.CategoryHomology.Bar

variable {C : Type u} [Category.{v} C]
variable [UnivLE.{max u v, w}]

/-- The additive coefficient structure of the simplicial bar construction. -/
@[stacks 08PG "additivity of the simplicial bar construction"]
instance simplicialObjectFunctor.additive :
    (simplicialObjectFunctor (C := C)).Additive := sorry

/-- The bar chain-complex functor in the coefficient presheaf. -/
@[stacks 08PG "functorial bar chain complex"]
noncomputable abbrev complexFunctor :
    (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ ChainComplex AddCommGrpCat.{w} ℕ :=
  simplicialObjectFunctor (C := C) ⋙
    AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{w}

/-- Evaluation of the bar chain-complex functor on a coefficient presheaf. -/
@[simp, stacks 08PG "bar chain-complex functor object formula"]
theorem complexFunctor_obj (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) :
    (complexFunctor (C := C)).obj F = CategoryHomology.complex F := sorry

/-- Evaluation of the bar chain-complex functor on a coefficient morphism. -/
@[simp, stacks 08PG "bar chain-complex functor map formula"]
theorem complexFunctor_map
    {F G : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (f : F ⟶ G) :
    (complexFunctor (C := C)).map f =
      CategoryHomology.complexMap (𝟭 C) f := sorry

/-- The bar chain-complex functor is additive. -/
@[stacks 08PG "additivity of the bar chain-complex functor"]
instance complexFunctor.additive :
    (complexFunctor (C := C)).Additive := sorry

/-- The bar chain-complex functor preserves finite limits. -/
@[stacks 08PG "finite-limit preservation of the bar chain-complex functor"]
instance complexFunctor.preservesFiniteLimits :
    PreservesFiniteLimits (complexFunctor (C := C)) := sorry

/-- The bar chain-complex functor preserves finite colimits. -/
@[stacks 08PG "finite-colimit preservation of the bar chain-complex functor"]
instance complexFunctor.preservesFiniteColimits :
    PreservesFiniteColimits (complexFunctor (C := C)) := sorry

/-- The bar chain-complex functor is exact in coefficients. -/
@[stacks 08PG "exactness of the bar chain-complex functor"]
theorem complexFunctor_exact :
    exactFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{w})
      (ChainComplex AddCommGrpCat.{w} ℕ) (complexFunctor (C := C)) := sorry

/-- The bar chain-complex functor bundled with its exactness property. -/
@[stacks 08PG "bundled exact bar chain-complex functor"]
noncomputable def complexExactFunctor :
    (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ₑ ChainComplex AddCommGrpCat.{w} ℕ :=
  ⟨complexFunctor (C := C), complexFunctor_exact (C := C)⟩

/-- The homological delta functor of the explicit bar construction. -/
@[stacks 08PG "category homology bar delta functor"]
noncomputable def deltaFunctor :
    HomologicalDeltaFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{w}) AddCommGrpCat.{w} :=
  HomologicalDeltaFunctor.ExactComplex.functorBundled (complexExactFunctor (C := C))

/-- The degree branches of the bar delta functor are the bar coefficient functors. -/
@[simp, stacks 08PG "bar delta functor degree formula"]
theorem deltaFunctor_obj (n : ℕ) :
    ((deltaFunctor (C := C) n).obj) =
      coefficientFunctor (C := C) n := sorry

/-- Objectwise evaluation of a bar delta-functor degree is category homology. -/
@[simp, stacks 08PG "bar delta functor object formula"]
theorem deltaFunctor_obj_obj
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    ((deltaFunctor (C := C) n).obj).obj F = homology (C := C) F n := sorry

/-- The connecting map of the bar delta functor is the boundary map of the bar chain-complex
functor. -/
@[simp, stacks 08PG "bar delta functor connecting formula"]
theorem deltaFunctor_δ
    {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat.{w})}
    (hS : S.ShortExact) (n : ℕ) :
    (deltaFunctor (C := C)).δ hS n =
      HomologicalDeltaFunctor.ExactComplex.connecting
        (complexExactFunctor (C := C)).1 hS n := sorry

/-- Positive bar homology is coeffaceable in the coefficient presheaf. -/
@[stacks 08PG "coeffaceability of positive bar homology"]
theorem coefficientFunctor_isCoeffaceable (n : ℕ) (hn : 0 < n) :
    (coefficientFunctor (C := C) n).IsCoeffaceable := sorry

/-- Every positive degree of the Bar delta functor is coeffaceable. -/
@[stacks 08PG "coeffaceability of positive Bar delta-functor degrees"]
theorem deltaFunctor_degree_isCoeffaceable (n : ℕ) (hn : 0 < n) :
    ((deltaFunctor (C := C) n).obj).IsCoeffaceable := sorry

/-- The bar homological delta functor is universal. -/
@[stacks 08PG "universality of the bar homological delta functor"]
instance deltaFunctor.isUniversal :
    HomologicalDeltaFunctor.IsUniversal (deltaFunctor (C := C)) := sorry

section ColimitComparison

variable [HasColimitsOfShape Cᵒᵖ AddCommGrpCat.{w}]

/-- The degree-zero branch of the bar delta functor is canonically the presheaf colimit. -/
@[stacks 08PG "degree-zero bar delta functor is colimit"]
noncomputable def deltaFunctorZeroIso :
    ((deltaFunctor (C := C) 0).obj) ≅
      (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}) :=
  eqToIso (deltaFunctor_obj (C := C) 0) ≪≫ zeroIso (C := C)

/-- The canonical comparison from any universal homological delta functor extending colimit to
the bar delta functor.  Its maps are obtained through the reusable universal-extension API from
the explicit degree-zero isomorphism. -/
@[stacks 08PG "universal category-homology comparison with the bar delta functor"]
noncomputable def universalIso
    (T : HomologicalDeltaFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{w}) AddCommGrpCat.{w})
    [T.IsUniversal]
    (e₀ : (T 0).obj ≅
      (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w})) :
    T ≅ deltaFunctor (C := C) :=
  HomologicalDeltaFunctor.IsUniversal.iso
    (e₀ ≪≫ (deltaFunctorZeroIso (C := C)).symm)

/-- The degree-zero component of `universalIso` is the supplied colimit comparison followed by
the explicit inverse of the bar degree-zero comparison. -/
@[simp, stacks 08PG "universal bar comparison degree-zero component"]
theorem universalIso_hom_app_zero
    (T : HomologicalDeltaFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{w}) AddCommGrpCat.{w})
    [T.IsUniversal]
    (e₀ : (T 0).obj ≅
      (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w})) :
    (universalIso (C := C) T e₀).hom.app 0 =
      (e₀ ≪≫ (deltaFunctorZeroIso (C := C)).symm).hom := sorry

end ColimitComparison

end CategoryTheory.CategoryHomology.Bar
