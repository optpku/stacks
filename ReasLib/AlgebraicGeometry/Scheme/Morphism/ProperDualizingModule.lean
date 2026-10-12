/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.DualizingModule
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Support
public import ReasLib.AlgebraicGeometry.Scheme.Dimension.Zero
public import ReasLib.AlgebraicGeometry.Scheme.Module.Depth
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.InternalHom.AffineComparison
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ExceptionalInverseImage

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- For a proper morphism from a scheme of topological dimension `d` to the spectrum of a
local Noetherian ring, the degree `-d` cohomology of the exceptional inverse image of a
normalized dualizing complex is a dualizing module. -/
theorem isDualizingModule_of_proper
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (ωA : DerivedCategory (ModuleCat.{u} A))
    (hωA : ωA.IsNormalizedDualizingComplex HA)
    (ωS : RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace)
    (hωS : IsIsomorphic ωS ((ModuleDerived.InternalHom.affineTildeDerived A).obj ωA))
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (fShriek : ExceptionalInverseImage f)
    (d : ℕ) (h_dimension : topologicalKrullDim X = d) :
    RingedSpace.ModuleDerived.IsDualizingModule
      (fShriek.functor.obj ωS) HX (-(d : ℤ))
      (RingedSpace.ModuleDerived.cohomologySheaf (fShriek.functor.obj ωS) (-(d : ℤ))) := sorry

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.ExceptionalInverseImage

/-- Nonzero cohomology of the exceptional inverse image of a normalized dualizing complex
occurs only in degrees between the negative dimension and zero. -/
theorem nonzeroCohomology_degreeBounds
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (ωA : DerivedCategory (ModuleCat.{u} A))
    (hωA : ωA.IsNormalizedDualizingComplex HA)
    (ωS : RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace)
    (hωS : IsIsomorphic ωS ((ModuleDerived.InternalHom.affineTildeDerived A).obj ωA))
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (fShriek : ExceptionalInverseImage f)
    (d : ℕ) (h_dimension : topologicalKrullDim X = d) (i : ℤ)
    (hi : ¬ IsZero (RingedSpace.ModuleDerived.cohomologySheaf
      (fShriek.functor.obj ωS) i)) :
    -(d : ℤ) ≤ i ∧ i ≤ 0 := sorry

/-- The support of each cohomology sheaf of the exceptional inverse image has dimension
at most the opposite of its nonpositive degree. -/
theorem cohomology_supportDimension_le
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (ωA : DerivedCategory (ModuleCat.{u} A))
    (hωA : ωA.IsNormalizedDualizingComplex HA)
    (ωS : RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace)
    (hωS : IsIsomorphic ωS ((ModuleDerived.InternalHom.affineTildeDerived A).obj ωA))
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (fShriek : ExceptionalInverseImage f)
    (d : ℕ) (h_dimension : topologicalKrullDim X = d) (i : ℤ) :
    topologicalKrullDim
        (RingedSpace.moduleSupport (RingedSpace.ModuleDerived.cohomologySheaf
          (fShriek.functor.obj ωS) i)) ≤
      if i ≤ 0 then ((-i).toNat : WithBot ℕ∞) else ⊥ := sorry

/-- The support of the degree-negative-d dualizing module is the union of the
irreducible components having the same dimension as the scheme. -/
theorem dualizingModule_support_eq_topComponents
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (ωA : DerivedCategory (ModuleCat.{u} A))
    (hωA : ωA.IsNormalizedDualizingComplex HA)
    (ωS : RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace)
    (hωS : IsIsomorphic ωS ((ModuleDerived.InternalHom.affineTildeDerived A).obj ωA))
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (fShriek : ExceptionalInverseImage f)
    (d : ℕ) (h_dimension : topologicalKrullDim X = d) :
    RingedSpace.moduleSupport (RingedSpace.ModuleDerived.cohomologySheaf
        (fShriek.functor.obj ωS) (-(d : ℤ))) =
      ⋃ Z : irreducibleComponents X,
        ⋃ (_ : topologicalKrullDim Z = topologicalKrullDim X), (Z : Set X) := sorry

/-- The degree-negative-d dualizing module satisfies Serre's condition `(S₂)`. -/
theorem dualizingModule_satisfiesSerreConditionSTwo
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (ωA : DerivedCategory (ModuleCat.{u} A))
    (hωA : ωA.IsNormalizedDualizingComplex HA)
    (ωS : RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace)
    (hωS : IsIsomorphic ωS ((ModuleDerived.InternalHom.affineTildeDerived A).obj ωA))
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (fShriek : ExceptionalInverseImage f)
    (d : ℕ) (h_dimension : topologicalKrullDim X = d) :
    @Scheme.Modules.satisfiesSerreConditionS X
      (LocallyOfFiniteType.isLocallyNoetherian f)
      (RingedSpace.ModuleDerived.cohomologySheaf
        (fShriek.functor.obj ωS) (-(d : ℤ)))
      (AlgebraicGeometry.Scheme.isDualizingModule_of_proper
        HA HX ωA hωA ωS hωS f fShriek d h_dimension).coherent 2 := sorry

end AlgebraicGeometry.Scheme.ExceptionalInverseImage
