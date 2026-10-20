module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FiberBetti

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- The degreewise fiber Betti function is provided by the shared mathematical owner. -/
#check
  (AlgebraicGeometry.Scheme.ModuleDerived.fiberBetti :
    {X : Scheme.{u}} → RingedSpace.ModuleDerived X.toRingedSpace → ℤ → X → ℕ)

/- The shared computation theorem identifies fiber Betti numbers with residue-field finrank. -/
#check
  (AlgebraicGeometry.Scheme.ModuleDerived.fiberBetti_apply :
    {X : Scheme.{u}} → (E : RingedSpace.ModuleDerived X.toRingedSpace) →
      (i : ℤ) → (x : X) →
      AlgebraicGeometry.Scheme.ModuleDerived.fiberBetti E i x =
        Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk x))
          (DerivedCategory.ResidueField.homology
            (X.presheaf.stalk x) (RingedSpace.ModuleDerived.Stalk.obj E x) i))

/- The shared fiber Betti function is invariant under isomorphism. -/
#check
  (AlgebraicGeometry.Scheme.ModuleDerived.fiberBetti_eq_of_iso :
    {X : Scheme.{u}} → {E F : RingedSpace.ModuleDerived X.toRingedSpace} →
      (E ≅ F) → (i : ℤ) →
      AlgebraicGeometry.Scheme.ModuleDerived.fiberBetti E i =
        AlgebraicGeometry.Scheme.ModuleDerived.fiberBetti F i)

/- Pseudo-coherence makes every residue-field fiber cohomology group finite-dimensional. -/
#check
  (AlgebraicGeometry.Scheme.ModuleDerived.fiberCohomology_finiteDimensional_of_isPseudoCoherent :
    {X : Scheme.{u}} → (E : RingedSpace.ModuleDerived X.toRingedSpace) →
      RingedSpace.ModuleDerived.IsPseudoCoherent E → (x : X) → (i : ℤ) →
      FiniteDimensional (IsLocalRing.ResidueField (X.presheaf.stalk x))
        (DerivedCategory.ResidueField.homology
          (X.presheaf.stalk x) (RingedSpace.ModuleDerived.Stalk.obj E x) i))
