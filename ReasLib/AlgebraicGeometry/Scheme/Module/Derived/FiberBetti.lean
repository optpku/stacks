module

public import Mathlib.Topology.Constructible
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import ReasLib.Algebra.Homology.DerivedCategory.ResidueField.MinimalFreeModel
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Stalk

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

variable {X : Scheme.{u}}

/-- The degree-`i` dimension of the derived residue-field fiber of `E` at `x`. -/
noncomputable def fiberBetti
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (i : ℤ) (x : X) : ℕ :=
  Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk x))
    (DerivedCategory.ResidueField.homology
      (X.presheaf.stalk x) (RingedSpace.ModuleDerived.Stalk.obj E x) i)

/-- The fiber Betti number is the finrank of residue-field homology. -/
theorem fiberBetti_apply
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (i : ℤ) (x : X) :
    fiberBetti E i x =
      Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk x))
        (DerivedCategory.ResidueField.homology
          (X.presheaf.stalk x) (RingedSpace.ModuleDerived.Stalk.obj E x) i) := sorry

/-- Isomorphic derived modules have the same degreewise fiber Betti functions. -/
theorem fiberBetti_eq_of_iso
    {E F : RingedSpace.ModuleDerived X.toRingedSpace} (e : E ≅ F) (i : ℤ) :
    fiberBetti E i = fiberBetti F i := sorry

/-- A pseudo-coherent derived module has finite-dimensional residue-field fiber cohomology in
every degree. -/
theorem fiberCohomology_finiteDimensional_of_isPseudoCoherent
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPseudoCoherent E) (x : X) (i : ℤ) :
    FiniteDimensional (IsLocalRing.ResidueField (X.presheaf.stalk x))
      (DerivedCategory.ResidueField.homology
        (X.presheaf.stalk x) (RingedSpace.ModuleDerived.Stalk.obj E x) i) := sorry

/-- Formation of the degreewise fiber Betti function of a pseudo-coherent derived module
commutes with arbitrary scheme base change. -/
theorem fiberBetti_pullback {X Y : Scheme.{u}} (f : Y ⟶ X)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPseudoCoherent E) (i : ℤ) :
    fiberBetti ((RingedSpace.modulePullbackDerived f.toShHom).obj E) i =
      fun y : Y ↦ fiberBetti E i (f y) := sorry

/-- Every degreewise fiber Betti function of a pseudo-coherent derived module is upper
semicontinuous. -/
theorem fiberBetti_upperSemicontinuous {X : Scheme.{u}}
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPseudoCoherent E) (i : ℤ) :
    UpperSemicontinuous (fiberBetti E i) := sorry

/-- Every level set of a degreewise fiber Betti function of a pseudo-coherent derived module
is locally constructible. -/
theorem fiberBetti_levelSet_isLocallyConstructible {X : Scheme.{u}}
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPseudoCoherent E) (i : ℤ) (n : ℕ) :
    Topology.IsLocallyConstructible ((fiberBetti E i) ⁻¹' {n}) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
