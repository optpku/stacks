/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.QuasiIso
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Triangulated
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Resolution
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Comparison
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated
public import ReasLib.CategoryTheory.Pretriangulated.Functor.Localization.Lift

@[expose] public section

open CategoryTheory
open CategoryTheory.Localization
open CategoryTheory.ObjectProperty
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- Bounded homotopy objects of `X.Modules` whose terms are finite locally free. This is
`Kᵇ(𝒜)` for the additive category `𝒜` of finite locally free `𝒪_X`-modules. -/
def boundedFiniteLocallyFreeHomotopy (X : Scheme.{u}) :
    ObjectProperty (HomotopyCategory X.Modules (up ℤ)) :=
  fun K ↦ SheafOfModules.CochainComplex.IsBoundedFiniteLocallyFree K.as

/-- Membership in `boundedFiniteLocallyFreeHomotopy X` is bounded finite local freeness of
the underlying complex. -/
theorem boundedFiniteLocallyFreeHomotopy_iff (X : Scheme.{u})
    (K : HomotopyCategory X.Modules (up ℤ)) :
    boundedFiniteLocallyFreeHomotopy X K ↔
      SheafOfModules.CochainComplex.IsBoundedFiniteLocallyFree K.as := sorry

/-- The homotopy category `Kᵇ(𝒜)` of bounded complexes of finite locally free
`𝒪_X`-modules. -/
abbrev BoundedFiniteLocallyFreeHomotopy (X : Scheme.{u}) :=
  (boundedFiniteLocallyFreeHomotopy X).FullSubcategory

namespace BoundedFiniteLocallyFreeHomotopy

/-- An object of `BoundedFiniteLocallyFreeHomotopy X` has a bounded finite locally free
underlying complex. -/
theorem property (X : Scheme.{u}) (K : BoundedFiniteLocallyFreeHomotopy X) :
    SheafOfModules.CochainComplex.IsBoundedFiniteLocallyFree K.obj.as := sorry

/-- Bounded finite locally free homotopy objects form a triangulated subcategory. -/
instance isTriangulated (X : Scheme.{u}) :
    (boundedFiniteLocallyFreeHomotopy X).IsTriangulated := sorry

/-- The derived image of a bounded finite locally free homotopy object is perfect. -/
theorem qh_obj_isPerfect (X : Scheme.{u})
    (K : BoundedFiniteLocallyFreeHomotopy X) :
    RingedSpace.ModuleDerived.IsPerfect (DerivedCategory.Qh.obj K.obj) := sorry

/-- The canonical functor from `Kᵇ(𝒜)` to perfect derived `𝒪_X`-modules. -/
noncomputable def toPerfect (X : Scheme.{u}) :
    BoundedFiniteLocallyFreeHomotopy X ⥤
      @RingedSpace.ModuleDerived.Perfect X.toRingedSpace :=
  FullSubcategory.restrict DerivedCategory.Qh
    (fun K hK ↦ qh_obj_isPerfect X ⟨K, hK⟩)

/-- On objects, `toPerfect X` is the derived localization functor `DerivedCategory.Qh`. -/
theorem toPerfect_obj (X : Scheme.{u})
    (K : BoundedFiniteLocallyFreeHomotopy X) :
    ((toPerfect X).obj K).obj = DerivedCategory.Qh.obj K.obj := sorry

/-- The source inclusion followed by `DerivedCategory.Qh` commutes with integer shifts. -/
noncomputable instance inclusionQh_commShift (X : Scheme.{u}) :
    ((boundedFiniteLocallyFreeHomotopy X).ι ⋙
      DerivedCategory.Qh).CommShift ℤ :=
  Functor.CommShift.comp (boundedFiniteLocallyFreeHomotopy X).ι
    DerivedCategory.Qh

/-- The restricted homotopy-to-derived functor carries its canonical compatibility with
integer shifts. -/
noncomputable instance toPerfect_commShift (X : Scheme.{u}) :
    (toPerfect X).CommShift ℤ :=
  @Functor.CommShift.ofComp _ _ _ _ _ _ _ _ _
    (@FullSubcategory.restrict.compιIso _ _ _ _
      (boundedFiniteLocallyFreeHomotopy X)
      (@RingedSpace.ModuleDerived.perfect X.toRingedSpace) DerivedCategory.Qh
      (fun K hK ↦ qh_obj_isPerfect X ⟨K, hK⟩)) _ _ ℤ _ _ _ _ _
        (inclusionQh_commShift X)

/-- The canonical functor from bounded finite locally free homotopy objects to perfect derived
objects is exact. -/
instance toPerfect_isTriangulated (X : Scheme.{u}) :
    (toPerfect X).IsTriangulated := sorry

/-- Quasi-isomorphisms in `Kᵇ(𝒜)`, obtained by restricting homotopy-category
quasi-isomorphisms. -/
abbrev quasiIso (X : Scheme.{u}) :
    MorphismProperty (BoundedFiniteLocallyFreeHomotopy X) :=
  fullSubcategoryLocalizationSystem (boundedFiniteLocallyFreeHomotopy X)
    (HomotopyCategory.quasiIso X.Modules (up ℤ))

/-- Restricted quasi-isomorphisms form a saturated multiplicative system. -/
instance quasiIso_isSaturatedMultiplicativeSystem (X : Scheme.{u}) :
    (quasiIso X).IsSaturatedMultiplicativeSystem := sorry

/-- A morphism in `Kᵇ(𝒜)` is in `quasiIso X` exactly when its underlying homotopy-category
morphism is a quasi-isomorphism. -/
theorem quasiIso_iff (X : Scheme.{u})
    {K L : BoundedFiniteLocallyFreeHomotopy X} (f : K ⟶ L) :
    quasiIso X f ↔ HomotopyCategory.quasiIso X.Modules (up ℤ) f.hom := sorry

/-- The canonical functor to perfect derived objects inverts quasi-isomorphisms. -/
theorem quasiIso_isInvertedBy_toPerfect (X : Scheme.{u}) :
    (quasiIso X).IsInvertedBy (toPerfect X) := sorry

/-- The functor from `S⁻¹Kᵇ(𝒜)` to perfect derived `𝒪_X`-modules induced by the canonical
functor, where `S` is the system of quasi-isomorphisms. -/
noncomputable def localizationFunctor (X : Scheme.{u}) :
    (quasiIso X).Localization ⥤
      @RingedSpace.ModuleDerived.Perfect X.toRingedSpace :=
  Localization.lift (toPerfect X) (quasiIso_isInvertedBy_toPerfect X) (quasiIso X).Q

/-- The induced functor out of `S⁻¹Kᵇ(𝒜)` factors the canonical functor. -/
noncomputable def localizationFunctorFacIso (X : Scheme.{u}) :
    (quasiIso X).Q ⋙ localizationFunctor X ≅ toPerfect X :=
  Localization.fac (toPerfect X) (quasiIso_isInvertedBy_toPerfect X) (quasiIso X).Q

/-- The induced localization functor carries the canonical compatibility with integer shifts. -/
noncomputable instance localizationFunctor_commShift (X : Scheme.{u}) :
    (localizationFunctor X).CommShift ℤ :=
  Localization.liftCommShift (quasiIso X) (quasiIso X).Q
    (toPerfect X) (quasiIso_isInvertedBy_toPerfect X)

/-- Naturality of the factorization of the canonical functor through `S⁻¹Kᵇ(𝒜)`. -/
theorem localizationFunctorFacIso_naturality (X : Scheme.{u})
    {K L : BoundedFiniteLocallyFreeHomotopy X} (f : K ⟶ L) :
    (localizationFunctor X).map ((quasiIso X).Q.map f) ≫
        (localizationFunctorFacIso X).hom.app L =
      (localizationFunctorFacIso X).hom.app K ≫ (toPerfect X).map f := sorry

/-- The induced functor from the localization to perfect derived objects is exact. -/
instance localizationFunctor_isTriangulated (X : Scheme.{u}) :
    (localizationFunctor X).IsTriangulated := sorry

/-- If `X` is quasi-compact and quasi-separated and has the resolution property, the exact
functor from bounded complexes of finite locally free `𝒪_X`-modules to perfect derived objects
factors through an equivalence `S⁻¹Kᵇ(𝒜) ⥤ D_perf(𝒪_X)`, where `S` consists of
quasi-isomorphisms. -/
theorem localizationFunctor_isEquivalence {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (hX : HasResolutionProperty X) :
    (localizationFunctor X).IsEquivalence := sorry

end BoundedFiniteLocallyFreeHomotopy

end AlgebraicGeometry.Scheme
