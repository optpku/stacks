module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.Preservation
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.BaseChange.RelativeDualizing
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Perfect
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Gorenstein
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Relative
public import ReasLib.RingTheory.RingHom.Perfect.Flat
public import ReasLib.RingTheory.RingHom.Fiber.FiniteType
public import ReasLib.RingTheory.Algebra.TensorProduct.Noetherian

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.ModuleCat
open CategoryTheory.ModuleCat.UpperShriek
open DerivedCategory.TStructure
open scoped TensorProduct

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.UpperShriek.Presentation

/-- A perfect finite-type map has a presentation-relative dualizing object with bounded finite
cohomology over the target ring. -/
theorem relativeDualizing_boundedFiniteCohomology_of_isPerfect
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsNoetherianRing A] [Algebra.FiniteType R A]
    [(algebraMap R A).IsPerfectRingMap]
    (p : Presentation (algebraMap R A)) :
    ((t.bounded : ObjectProperty (DerivedCategory (ModuleCat.{u, u} A))) ⊓
        DerivedCategory.cohomologyIn (ModuleCat.isFG A))
      (p.functor.obj (ModuleCat.single0 (ModuleCat.of R R))) := sorry

/-- A perfect finite-type map gives finite Tor dimension over the base for its
presentation-relative dualizing object. -/
theorem relativeDualizing_hasFiniteTorDimension_of_isPerfect
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsNoetherianRing A] [Algebra.FiniteType R A]
    [(algebraMap R A).IsPerfectRingMap]
    (p : Presentation (algebraMap R A)) :
    (p.functor.obj (ModuleCat.single0 (ModuleCat.of R R))).HasFiniteTorDimensionOver R := sorry

/-- For a perfect finite-type map, the canonical homothety of the
presentation-relative dualizing object is an isomorphism. -/
theorem relativeDualizing_homothety_isIso_of_isPerfect
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsNoetherianRing A] [Algebra.FiniteType R A]
    [(algebraMap R A).IsPerfectRingMap]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u, u} A))]
    (p : Presentation (algebraMap R A))
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u, u} A))) :
    let ω := p.functor.obj (ModuleCat.single0 (ModuleCat.of R R))
    IsIso (@MonoidalClosed.curry'
      (DerivedCategory (ModuleCat.{u, u} A)) _ _ ω ω (HA.closed ω) (𝟙 ω)) := sorry

/-- A flat finite-type map has a presentation-relative dualizing object with bounded finite
cohomology over the target ring. -/
theorem relativeDualizing_boundedFiniteCohomology_of_flat
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsNoetherianRing A] [Algebra.FiniteType R A] [Module.Flat R A]
    (p : Presentation (algebraMap R A)) :
    ((t.bounded : ObjectProperty (DerivedCategory (ModuleCat.{u, u} A))) ⊓
        DerivedCategory.cohomologyIn (ModuleCat.isFG A))
      (p.functor.obj (ModuleCat.single0 (ModuleCat.of R R))) := sorry

/-- A flat finite-type map gives finite Tor dimension over the base for its
presentation-relative dualizing object. -/
theorem relativeDualizing_hasFiniteTorDimension_of_flat
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsNoetherianRing A] [Algebra.FiniteType R A] [Module.Flat R A]
    (p : Presentation (algebraMap R A)) :
    (p.functor.obj (ModuleCat.single0 (ModuleCat.of R R))).HasFiniteTorDimensionOver R := sorry

/-- For a flat finite-type map, the canonical homothety of the presentation-relative dualizing
object is an isomorphism. -/
theorem relativeDualizing_homothety_isIso_of_flat
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsNoetherianRing A] [Algebra.FiniteType R A] [Module.Flat R A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u, u} A))]
    (p : Presentation (algebraMap R A))
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u, u} A))) :
    let ω := p.functor.obj (ModuleCat.single0 (ModuleCat.of R R))
    IsIso (@MonoidalClosed.curry'
      (DerivedCategory (ModuleCat.{u, u} A)) _ _ ω ω (HA.closed ω) (𝟙 ω)) := sorry

/-- For a flat finite-type map, the presentation-relative dualizing object is perfect over the
base ring. -/
theorem relativeDualizing_isPerfectOver_of_flat
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsNoetherianRing A] [Algebra.FiniteType R A] [Module.Flat R A]
    (p : Presentation (algebraMap R A)) :
    (p.functor.obj (ModuleCat.single0 (ModuleCat.of R R))).IsPerfectOver R := sorry

/-- For a flat finite-type map between Noetherian rings, the presentation-relative
dualizing object is a relative dualizing complex over the base ring. -/
theorem relativeDualizing_isRelativeDualizingComplex_of_flat
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsNoetherianRing A] [Algebra.FiniteType R A] [Module.Flat R A]
    (p : Presentation (algebraMap R A)) :
    @CategoryTheory.DerivedCategory.IsRelativeDualizingComplex R _ A _ _ inferInstance
      (Algebra.FinitePresentation.of_finiteType.mp inferInstance)
      (p.functor.obj (ModuleCat.single0 (ModuleCat.of R R))) := sorry

/-- After base change to any field over the base, the derived scalar extension of the
flat presentation-relative dualizing object is dualizing. -/
theorem relativeDualizing_baseChange_isDualizing_of_flat
    {R A k : Type u} [CommRing R] [CommRing A] [Field k]
    [Algebra R A] [Algebra R k] [IsNoetherianRing R] [IsNoetherianRing A]
    [Algebra.FiniteType R A] [Module.Flat R A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u, u} (A ⊗[R] k)))]
    (p : Presentation (algebraMap R A))
    (Hk : MonoidalClosed (DerivedCategory (ModuleCat.{u, u} (A ⊗[R] k)))) :
    let hNoetherian : IsNoetherianRing (A ⊗[R] k) :=
      Algebra.FiniteType.isNoetherianRing_tensor_left
    @CategoryTheory.DerivedCategory.IsDualizingComplex (A ⊗[R] k) _ hNoetherian _
      ((ModuleCat.derivedExtensionOfScalars
        (algebraMap A (A ⊗[R] k))).obj
          (p.functor.obj (ModuleCat.single0 (ModuleCat.of R R)))) Hk := sorry

/-- The relative dualizing object is invertible exactly when all residue-field fibers are Gorenstein. -/
theorem fibersGorenstein_iff_relativeDualizingIsInvertible
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsNoetherianRing A]
    [Algebra.FiniteType R A] [Module.Flat R A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u, u} A))]
    (T : @CategoryTheory.DerivedCategory.DerivedTensor.Right.Monoidal.Model
      (ModuleCat.{u, u} A) _ _ _ _ _ _ _)
    (p : Presentation (algebraMap R A)) :
    (∀ 𝓅 : PrimeSpectrum R, IsGorensteinRing (𝓅.asIdeal.Fiber A)) ↔
      MonoidalCategory.isInvertibleObject
        (p.functor.obj (ModuleCat.single0 (ModuleCat.of R R))) := sorry

end CategoryTheory.ModuleCat.UpperShriek.Presentation
