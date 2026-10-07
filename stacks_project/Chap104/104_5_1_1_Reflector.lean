module

public import ReasLib.CategoryTheory.Abelian.SerreQuotient
public import stacks_project.Chap104.Definition_104_5_1_LQCohFbc

/-!
# Serre quotient of fppf LQCoh^{fbc} by parasitic objects

The functor `Q : FppfModules.LQCohFbc X ⟶ FppfModules.LQCohFbc.Quotient X` is
the Serre quotient of locally quasi-coherent fppf modules with the flat base
change property by their parasitic objects. This is the constructible model of
the Stacks functor `Q` that kills `Parasitic ∩ LQCoh^{fbc}` inside
`Mod(X_fppf, 𝒪_X)`, matching the ambient category of `DerivedQCoh`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.FppfModules.LQCohFbc

variable {S : Scheme.{u}}

/-- Parasitic objects of `FppfModules.LQCohFbc X`, obtained by restricting
`FppfModules.parasitic` along the inclusion into fppf modules. -/
abbrev parasitic (X : GroupoidsOver S) [AlgebraicStack X] :
    ObjectProperty (FppfModules.LQCohFbc X) :=
  (FppfModules.parasitic X).inverseImage (FppfModules.inclusion X)

/-- An object of `FppfModules.LQCohFbc X` is parasitic if and only if its
underlying fppf module is parasitic. -/
theorem parasitic_iff {X : GroupoidsOver S} [AlgebraicStack X]
    (F : FppfModules.LQCohFbc X) :
    parasitic X F ↔ FppfModules.parasitic X ((FppfModules.inclusion X).obj F) :=
  sorry

/-- Membership in `parasitic X` is inverse image of `FppfModules.parasitic`
along `FppfModules.inclusion X`. -/
theorem mem_parasitic {X : GroupoidsOver S} [AlgebraicStack X]
    (F : FppfModules.LQCohFbc X) :
    parasitic X F ↔ FppfModules.parasitic X ((FppfModules.inclusion X).obj F) :=
  sorry

/-- Parasitic objects of `FppfModules.LQCohFbc X` form a Serre class. -/
instance parasitic_isSerreClass (X : GroupoidsOver S) [AlgebraicStack X] :
    IsSerreClass (parasitic X) := sorry

/-- The Serre quotient of `FppfModules.LQCohFbc X` by parasitic objects, used as
the constructible model of `QCoh(𝒪_X)` for the descended cohomology functors. -/
abbrev Quotient (X : GroupoidsOver S) [AlgebraicStack X] :=
  (parasitic X).isoModSerre.Localization

/-- `Quotient X` is the localization of `FppfModules.LQCohFbc X` at isomorphisms
modulo parasitic objects. -/
theorem Quotient_eq (X : GroupoidsOver S) [AlgebraicStack X] :
    Quotient X = (parasitic X).isoModSerre.Localization := sorry

/-- The Serre quotient functor `Q : FppfModules.LQCohFbc X ⥤ Quotient X`. -/
def toQCoh (X : GroupoidsOver S) [AlgebraicStack X] :
    FppfModules.LQCohFbc X ⥤ Quotient X :=
  (parasitic X).isoModSerre.Q

/-- `toQCoh X` is the canonical localization functor at
`(parasitic X).isoModSerre`. -/
theorem toQCoh_eq (X : GroupoidsOver S) [AlgebraicStack X] :
    toQCoh X = (parasitic X).isoModSerre.Q := sorry

/-- The kernel of `toQCoh X` is exactly the parasitic objects of
`FppfModules.LQCohFbc X`. -/
theorem toQCoh_kernel (X : GroupoidsOver S) [AlgebraicStack X] :
    Functor.kernel (toQCoh X) = parasitic X := sorry

/-- An object of `FppfModules.LQCohFbc X` becomes zero after `toQCoh` if and
only if it is parasitic. -/
theorem toQCoh_isZero_iff {X : GroupoidsOver S} [AlgebraicStack X]
    (F : FppfModules.LQCohFbc X) :
    IsZero ((toQCoh X).obj F) ↔ parasitic X F := sorry

/-- `toQCoh X` is an exact functor of abelian categories. -/
theorem toQCoh_exact (X : GroupoidsOver S) [AlgebraicStack X] :
    exactFunctor (FppfModules.LQCohFbc X) (Quotient X) (toQCoh X) := sorry

end AlgebraicGeometry.GroupoidsOver.FppfModules.LQCohFbc
