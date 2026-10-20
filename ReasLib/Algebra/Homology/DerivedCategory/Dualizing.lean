/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.InjectiveAmplitude
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.Closed
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.Closed.Bifunctor
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.Unit
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.RHom
public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality
public import Mathlib.RingTheory.Noetherian.Defs

@[expose] public section

open CategoryTheory
open scoped MonoidalCategory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory

/-- A closed presentation of the derived category together with the comparison data identifying
the canonical module `RHom` and its regular degree-zero unit with that presentation.  The
comparison and unit are explicit because a derived category does not carry a globally selected
monoidal or closed structure. -/
structure CanonicalClosedPresentation
    {A : Type u} [CommRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))] where
  /-- The explicit comparison from canonical module `RHom` to the selected internal Hom. -/
  comparison :
    InternalHom.RHom.BifunctorComparison (A := A)
  /-- The explicit identification of the regular degree-zero object with the selected tensor unit. -/
  unitIso :
    InternalHom.RHom.Unit.single (A := A) ≅
      𝟙_ (DerivedCategory (ModuleCat.{u} A))

namespace CanonicalClosedPresentation

/-- Construct a canonical closed presentation from its comparison and unit data. -/
def of
    {A : Type u} [CommRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (comparison : InternalHom.RHom.BifunctorComparison (A := A))
    (unitIso :
      InternalHom.RHom.Unit.single (A := A) ≅
        𝟙_ (DerivedCategory (ModuleCat.{u} A))) :
    CanonicalClosedPresentation (A := A) :=
  ⟨comparison, unitIso⟩

end CanonicalClosedPresentation

/-- The canonical homothety from the regular degree-zero object to the derived endomorphism
object, transported through an explicit closed presentation. -/
noncomputable def canonicalHomothety
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (C : CanonicalClosedPresentation (A := A))
    (K : DerivedCategory (ModuleCat.{u} A)) :
    InternalHom.RHom.Unit.single (A := A) ⟶
      InternalHom.RHom.obj (A := A) K K :=
  C.unitIso.hom ≫
    @MonoidalClosed.curry'
      (DerivedCategory (ModuleCat.{u} A)) _ _ K K
      (C.comparison.closed.closed K) (𝟙 K) ≫
      (C.comparison.objIso K K).inv

/-- A derived module complex is dualizing relative to an explicit canonical closed presentation
when it has finite injective dimension, finite cohomology modules in every degree, and invertible
canonical `RHom` homothety. -/
structure IsCanonicalDualizingComplex
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (K : DerivedCategory (ModuleCat.{u} A))
    (C : CanonicalClosedPresentation (A := A)) : Prop where
  /-- The complex has finite injective dimension. -/
  finiteInjectiveDimension : K.HasFiniteInjectiveDimension
  /-- Every cohomology module of the complex is finite. -/
  finiteCohomology :
    ∀ i : ℤ, Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)
  /-- The canonical homothety from the regular degree-zero object to `RHom(K, K)` is invertible. -/
  homothety_isIso : IsIso (canonicalHomothety C K)

namespace IsCanonicalDualizingComplex

/-- Construct the canonical dualizing-complex property from its three defining conditions. -/
def ofConditions
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    {K : DerivedCategory (ModuleCat.{u} A)}
    (C : CanonicalClosedPresentation (A := A))
    (h_injective : K.HasFiniteInjectiveDimension)
    (h_finite :
      ∀ i : ℤ, Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K))
    (h_homothety : IsIso (canonicalHomothety C K)) :
    K.IsCanonicalDualizingComplex C :=
  ⟨h_injective, h_finite, h_homothety⟩

end IsCanonicalDualizingComplex

/-- The defining conditions for a canonical dualizing complex over a Noetherian commutative ring. -/
theorem isCanonicalDualizingComplex_iff
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (K : DerivedCategory (ModuleCat.{u} A))
    (C : CanonicalClosedPresentation (A := A)) :
    K.IsCanonicalDualizingComplex C ↔
      K.HasFiniteInjectiveDimension ∧
        (∀ i : ℤ,
          Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)) ∧
        IsIso (canonicalHomothety C K) := sorry

/-- A derived module complex over a Noetherian commutative ring is dualizing relative to a
selected closed-monoidal presentation when it has finite injective dimension, finite cohomology
modules in every degree, and invertible canonical homothety. -/
structure IsDualizingComplex
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (K : DerivedCategory (ModuleCat.{u} A))
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))) : Prop where
  /-- The complex has finite injective dimension. -/
  finiteInjectiveDimension : K.HasFiniteInjectiveDimension
  /-- Every cohomology module of the complex is finite. -/
  finiteCohomology :
    ∀ i : ℤ, Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)
  /-- The homothety in the selected closed presentation is invertible. -/
  homothety_isIso :
    IsIso (@MonoidalClosed.curry'
      (DerivedCategory (ModuleCat.{u} A)) _ _ K K (H.closed K) (𝟙 K))

namespace IsDualizingComplex

/-- Construct the dualizing-complex property from its three defining conditions. -/
def ofConditions
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    {K : DerivedCategory (ModuleCat.{u} A)}
    {H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))}
    (h_injective : K.HasFiniteInjectiveDimension)
    (h_finite :
      ∀ i : ℤ, Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K))
    (h_homothety :
      IsIso (@MonoidalClosed.curry'
        (DerivedCategory (ModuleCat.{u} A)) _ _ K K (H.closed K) (𝟙 K))) :
    K.IsDualizingComplex H :=
  ⟨h_injective, h_finite, h_homothety⟩

end IsDualizingComplex

/-- The defining conditions for a dualizing complex over a Noetherian commutative ring. -/
theorem isDualizingComplex_iff
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (K : DerivedCategory (ModuleCat.{u} A))
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))) :
    K.IsDualizingComplex H ↔
      K.HasFiniteInjectiveDimension ∧
        (∀ i : ℤ,
          Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)) ∧
        IsIso (@MonoidalClosed.curry'
          (DerivedCategory (ModuleCat.{u} A)) _ _ K K (H.closed K) (𝟙 K)) := sorry

end CategoryTheory.DerivedCategory
