module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Map.Naturality.Plus
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Below.Composition
public import ReasLib.CategoryTheory.Filtration.Derived.BoundedFunctor.RightDerived
public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact
public import ReasLib.CategoryTheory.Filtration.GradedPiece.Comparison
public import ReasLib.CategoryTheory.Functor.Derived.Composition.Right

/-!
# Graded pieces of filtered right-derived functors

This leaf owns the specialized natural isomorphism identifying the `p`-th associated-graded
piece of the filtered right-derived functor of a left-exact functor with the ordinary
right-derived functor of that graded piece.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.FilteredObject.FiniteDerived.Plus.LeftExact.GradedPiece

variable {A : Type u₁} {B : Type u₂}
  [_root_.CategoryTheory.Category.{v₁} A]
  [_root_.CategoryTheory.Category.{v₂} B]
  [Abelian A] [Abelian B]

/-- The functor sending a finite filtered object to the `p`-th graded piece of its image
under a left-exact functor. -/
noncomputable abbrev mappedFunctor (T : A ⥤ₗ B) (p : ℤ) :
    FilteredObject.Finite.category A ⥤ B :=
  FilteredObject.Finite.mapFunctor T.obj ⋙
    FilteredObject.Finite.AssociatedGraded.functor B ⋙ GradedObject.eval p

/-- The functor sending a finite filtered object to the image under a left-exact functor of
its `p`-th graded piece. -/
noncomputable abbrev termwiseFunctor (T : A ⥤ₗ B) (p : ℤ) :
    FilteredObject.Finite.category A ⥤ B :=
  FilteredObject.Finite.AssociatedGraded.functor A ⋙ GradedObject.eval p ⋙ T.obj

/-- The canonical projection from the `p`-th stage of a mapped finite filtered object to the
image of its original `p`-th graded piece. -/
noncomputable def projection (T : A ⥤ₗ B) (X : FilteredObject.Finite.category A) (p : ℤ) :
    (FilteredObject.map T.obj X.obj).stage p ⟶ T.obj.obj (X.obj.gradedPiece p) :=
  (Subobject.underlyingIso (T.obj.map (X.obj.filtration.stage p).arrow)).hom ≫
    T.obj.map (cokernel.π (X.obj.succInclusion p))

/-- The mapped successor inclusion is killed by the canonical graded-piece projection. -/
theorem succInclusion_comp_projection (T : A ⥤ₗ B)
    (X : FilteredObject.Finite.category A) (p : ℤ) :
    (FilteredObject.map T.obj X.obj).succInclusion p ≫ projection T X p = 0 := sorry

/-- The object-level comparison from the `p`-th graded piece after applying `T` to the image
under `T` of the original `p`-th graded piece. -/
noncomputable def comparison (T : A ⥤ₗ B) (p : ℤ) :
    mappedFunctor T p ⟶ termwiseFunctor T p where
  app X :=
    FilteredObject.GradedPiece.desc (FilteredObject.map T.obj X.obj) p
      (projection T X p) (succInclusion_comp_projection T X p)
  naturality := sorry

/-- The component of `comparison` is the cokernel descent of `projection`. -/
theorem comparison_app (T : A ⥤ₗ B) (X : FilteredObject.Finite.category A) (p : ℤ) :
    (comparison T p).app X =
      FilteredObject.GradedPiece.desc (FilteredObject.map T.obj X.obj) p
        (projection T X p) (succInclusion_comp_projection T X p) := sorry

/-- The bounded-below homotopy lift of the object-level graded-piece comparison. -/
noncomputable def homotopyComparison (T : A ⥤ₗ B) (p : ℤ) :
    (mappedFunctor T p).mapHomotopyCategoryPlus ⟶
      (termwiseFunctor T p).mapHomotopyCategoryPlus :=
  Functor.Homotopy.Plus.natTrans (comparison T p)

variable [HasDerivedCategory A] [HasDerivedCategory B]
variable [HasDerivedCategory (GradedObject ℤ A)]
  [HasDerivedCategory (GradedObject ℤ B)]

/-- The common uniqueness source obtained by applying the filtered homotopy functor of `T` and
then the `p`-th graded-piece functor. -/
noncomputable abbrev filteredSource (T : A ⥤ₗ B) (p : ℤ) :
    HomotopyCategory.Plus (FilteredObject.Finite.category A) ⥤ DerivedCategory.Plus B :=
  homotopy T ⋙ Plus.GradedPiece.homotopy B p

/-- The ordinary-path source obtained by taking the `p`-th graded piece and then the ordinary
right-derived functor of `T`. -/
noncomputable abbrev ordinarySource (T : A ⥤ₗ B) [EnoughInjectives A] (p : ℤ) :
    HomotopyCategory.Plus (FilteredObject.Finite.category A) ⥤ DerivedCategory.Plus B :=
  Plus.GradedPiece.homotopy A p ⋙ T.obj.rightDerivedFunctorPlus

/-- The iterated unit exhibiting `functor T ⋙ canonicalLift B p` as a right-derived functor of
`filteredSource`. -/
noncomputable def filteredFactorization (T : A ⥤ₗ B) [EnoughInjectives A] (p : ℤ) :
    filteredSource T p ⟶
      Plus.Quotient.canonicalFunctor A ⋙
        (functor T (AssociatedGraded.inverts A) (AssociatedGraded.inverts B) ⋙
          Plus.GradedPiece.canonicalLift B p) :=
  Functor.RightDerived.Composition.iteratedUnit
    (unit T (AssociatedGraded.inverts A) (AssociatedGraded.inverts B))
    (Plus.GradedPiece.canonicalFacIso B p).inv

/-- The ordinary factorization of `filteredSource` through `canonicalLift A p` and the ordinary
right-derived functor of `T`, obtained by lifting `comparison` to homotopy categories. -/
noncomputable def ordinaryFactorization (T : A ⥤ₗ B) [EnoughInjectives A] (p : ℤ) :
    filteredSource T p ⟶
      Plus.Quotient.canonicalFunctor A ⋙
        (Plus.GradedPiece.canonicalLift A p ⋙ T.obj.rightDerivedFunctorPlus) :=
  let grA := FilteredObject.Finite.AssociatedGraded.functor A ⋙ GradedObject.eval p
  let grB := FilteredObject.Finite.AssociatedGraded.functor B ⋙ GradedObject.eval p
  let mapT := FilteredObject.Finite.mapFunctor T.obj
  (Functor.toBoundedBelowDerived.compIso mapT grB).inv ≫
    Functor.whiskerRight (homotopyComparison T p)
      (DerivedCategory.Plus.Qh : HomotopyCategory.Plus B ⥤ DerivedCategory.Plus B) ≫
    (Functor.toBoundedBelowDerived.compIso grA T.obj).hom ≫
    Functor.whiskerLeft grA.mapHomotopyCategoryPlus T.obj.rightDerivedFunctorPlusUnit ≫
    (Functor.associator grA.mapHomotopyCategoryPlus
        (DerivedCategory.Plus.Qh : HomotopyCategory.Plus A ⥤ DerivedCategory.Plus A)
        T.obj.rightDerivedFunctorPlus).inv ≫
    Functor.whiskerRight (Plus.GradedPiece.canonicalFacIso A p).inv
      T.obj.rightDerivedFunctorPlus ≫
    (Functor.associator (Plus.Quotient.canonicalFunctor A)
        (Plus.GradedPiece.canonicalLift A p) T.obj.rightDerivedFunctorPlus).hom

/-- The filtered composite `gr^p ∘ RT` is a right-derived functor of `filteredSource`. -/
instance isRightDerived_filtered (T : A ⥤ₗ B) [EnoughInjectives A] (p : ℤ) :
    (functor T (AssociatedGraded.inverts A) (AssociatedGraded.inverts B) ⋙
        Plus.GradedPiece.canonicalLift B p).IsRightDerivedFunctor
      (filteredFactorization T p) (Plus.QuasiIso A) := sorry

/-- The ordinary composite `RT ∘ gr^p` is a right-derived functor of `filteredSource`. -/
instance isRightDerived_ordinary (T : A ⥤ₗ B) [EnoughInjectives A] (p : ℤ) :
    (Plus.GradedPiece.canonicalLift A p ⋙ T.obj.rightDerivedFunctorPlus).IsRightDerivedFunctor
      (ordinaryFactorization T p) (Plus.QuasiIso A) := sorry

/-- The canonical natural isomorphism `gr^p ∘ RT ≅ RT ∘ gr^p` on `DF⁺`, comparing the filtered
right-derived functor of a left-exact `T` with the ordinary right-derived functor of `T`. -/
noncomputable def iso (T : A ⥤ₗ B) [EnoughInjectives A] (p : ℤ) :
    functor T (AssociatedGraded.inverts A) (AssociatedGraded.inverts B) ⋙
        Plus.GradedPiece.canonicalLift B p ≅
      Plus.GradedPiece.canonicalLift A p ⋙ T.obj.rightDerivedFunctorPlus :=
  Plus.GradedPiece.RightDerived.canonicalIso p (filteredFactorization T p)
    (ordinaryFactorization T p)

namespace iso

variable (T : A ⥤ₗ B) [EnoughInjectives A] (p : ℤ)

/-- The specialized graded-piece comparison carries the filtered factorization to the ordinary
factorization. -/
@[reassoc (attr := simp)]
theorem fac :
    filteredFactorization T p ≫
        Functor.whiskerLeft (Plus.Quotient.canonicalFunctor A) (iso T p).hom =
      ordinaryFactorization T p := sorry

/-- Componentwise form of `iso.fac`. -/
@[simp]
theorem fac_app (X : HomotopyCategory.Plus (FilteredObject.Finite.category A)) :
    (filteredFactorization T p).app X ≫
        (iso T p).hom.app ((Plus.Quotient.canonicalFunctor A).obj X) =
      (ordinaryFactorization T p).app X := sorry

/-- The inverse specialized comparison carries the ordinary factorization back to the filtered
factorization. -/
@[reassoc (attr := simp)]
theorem inv_fac :
    ordinaryFactorization T p ≫
        Functor.whiskerLeft (Plus.Quotient.canonicalFunctor A) (iso T p).inv =
      filteredFactorization T p := sorry

/-- Componentwise form of `iso.inv_fac`. -/
@[simp]
theorem inv_fac_app (X : HomotopyCategory.Plus (FilteredObject.Finite.category A)) :
    (ordinaryFactorization T p).app X ≫
        (iso T p).inv.app ((Plus.Quotient.canonicalFunctor A).obj X) =
      (filteredFactorization T p).app X := sorry

end iso

end CategoryTheory.FilteredObject.FiniteDerived.Plus.LeftExact.GradedPiece
