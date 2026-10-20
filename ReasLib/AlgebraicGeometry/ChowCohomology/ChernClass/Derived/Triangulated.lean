module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Derived.EnvelopeDescent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Triangulated
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Representative.Morphism
public import ReasLib.AlgebraicGeometry.ChowCohomology.Completion.Integral

@[expose] public section

open CategoryTheory
open CategoryTheory.Pretriangulated

noncomputable section

universe u

namespace AlgebraicGeometry.ChernClass.Derived

open RingedSpace.ModuleDerived.Morphism

/-- The first vertex of a distinguished triangle of perfect derived modules has defined Chern
classes if the first morphism is representable by locally bounded finite locally free complexes
after an envelope pullback or on the scheme itself, or if every irreducible component is
quasi-compact or the scheme is quasi-compact. -/
theorem isDefined_obj₁_of_distinguished
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (T : Triangle (RingedSpace.ModuleDerived X.toRingedSpace))
    (hT : T ∈ distTriang (RingedSpace.ModuleDerived X.toRingedSpace))
    (h₁ : RingedSpace.ModuleDerived.IsPerfect T.obj₁)
    (h₂ : RingedSpace.ModuleDerived.IsPerfect T.obj₂)
    (h₃ : RingedSpace.ModuleDerived.IsPerfect T.obj₃)
    (h : (∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsEnvelope f ∧
        HasLocallyBoundedFiniteLocallyFree
          ((RingedSpace.modulePullbackDerived f.toShHom).map T.mor₁)) ∨
      HasLocallyBoundedFiniteLocallyFree T.mor₁ ∨
      (∀ Z : irreducibleComponents X, IsCompact (Z : Set X)) ∨ CompactSpace X) :
    IsDefined T.obj₁ := sorry

/-- The second vertex of a distinguished triangle of perfect derived modules has defined Chern
classes under the envelope representability, direct representability, or quasi-compactness
alternatives for the first morphism and the scheme. -/
theorem isDefined_obj₂_of_distinguished
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (T : Triangle (RingedSpace.ModuleDerived X.toRingedSpace))
    (hT : T ∈ distTriang (RingedSpace.ModuleDerived X.toRingedSpace))
    (h₁ : RingedSpace.ModuleDerived.IsPerfect T.obj₁)
    (h₂ : RingedSpace.ModuleDerived.IsPerfect T.obj₂)
    (h₃ : RingedSpace.ModuleDerived.IsPerfect T.obj₃)
    (h : (∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsEnvelope f ∧
        HasLocallyBoundedFiniteLocallyFree
          ((RingedSpace.modulePullbackDerived f.toShHom).map T.mor₁)) ∨
      HasLocallyBoundedFiniteLocallyFree T.mor₁ ∨
      (∀ Z : irreducibleComponents X, IsCompact (Z : Set X)) ∨ CompactSpace X) :
    IsDefined T.obj₂ := sorry

/-- The third vertex of a distinguished triangle of perfect derived modules has defined Chern
classes under the envelope representability, direct representability, or quasi-compactness
alternatives for the first morphism and the scheme. -/
theorem isDefined_obj₃_of_distinguished
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (T : Triangle (RingedSpace.ModuleDerived X.toRingedSpace))
    (hT : T ∈ distTriang (RingedSpace.ModuleDerived X.toRingedSpace))
    (h₁ : RingedSpace.ModuleDerived.IsPerfect T.obj₁)
    (h₂ : RingedSpace.ModuleDerived.IsPerfect T.obj₂)
    (h₃ : RingedSpace.ModuleDerived.IsPerfect T.obj₃)
    (h : (∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsEnvelope f ∧
        HasLocallyBoundedFiniteLocallyFree
          ((RingedSpace.modulePullbackDerived f.toShHom).map T.mor₁)) ∨
      HasLocallyBoundedFiniteLocallyFree T.mor₁ ∨
      (∀ Z : irreducibleComponents X, IsCompact (Z : Set X)) ∨ CompactSpace X) :
    IsDefined T.obj₃ := sorry

/-- Total Chern classes multiply along a distinguished triangle of perfect derived modules
under the envelope representability, direct representability, or quasi-compactness alternatives.
The product is finite Cauchy convolution in completed nonnegative Chow cohomology. -/
theorem totalClass_distinguished
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π] (classes : Theory δ π)
    (T : Triangle (RingedSpace.ModuleDerived X.toRingedSpace))
    (hT : T ∈ distTriang (RingedSpace.ModuleDerived X.toRingedSpace))
    (h₁ : RingedSpace.ModuleDerived.IsPerfect T.obj₁)
    (h₂ : RingedSpace.ModuleDerived.IsPerfect T.obj₂)
    (h₃ : RingedSpace.ModuleDerived.IsPerfect T.obj₃)
    (h : (∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsEnvelope f ∧
        HasLocallyBoundedFiniteLocallyFree
          ((RingedSpace.modulePullbackDerived f.toShHom).map T.mor₁)) ∨
      HasLocallyBoundedFiniteLocallyFree T.mor₁ ∨
      (∀ Z : irreducibleComponents X, IsCompact (Z : Set X)) ∨ CompactSpace X) :
    totalClass δ π classes T.obj₂ h₂
        (isDefined_obj₂_of_distinguished δ π T hT h₁ h₂ h₃ h) =
      totalClass δ π classes T.obj₁ h₁
          (isDefined_obj₁_of_distinguished δ π T hT h₁ h₂ h₃ h) *
        totalClass δ π classes T.obj₃ h₃
          (isDefined_obj₃_of_distinguished δ π T hT h₁ h₂ h₃ h) := sorry

/-- Chern characters add along a distinguished triangle of perfect derived modules under the
envelope representability, direct representability, or quasi-compactness alternatives. -/
theorem character_distinguished
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π] (classes : Theory δ π)
    (T : Triangle (RingedSpace.ModuleDerived X.toRingedSpace))
    (hT : T ∈ distTriang (RingedSpace.ModuleDerived X.toRingedSpace))
    (h₁ : RingedSpace.ModuleDerived.IsPerfect T.obj₁)
    (h₂ : RingedSpace.ModuleDerived.IsPerfect T.obj₂)
    (h₃ : RingedSpace.ModuleDerived.IsPerfect T.obj₃)
    (h : (∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsEnvelope f ∧
        HasLocallyBoundedFiniteLocallyFree
          ((RingedSpace.modulePullbackDerived f.toShHom).map T.mor₁)) ∨
      HasLocallyBoundedFiniteLocallyFree T.mor₁ ∨
      (∀ Z : irreducibleComponents X, IsCompact (Z : Set X)) ∨ CompactSpace X) :
    character δ π classes T.obj₂ h₂
        (isDefined_obj₂_of_distinguished δ π T hT h₁ h₂ h₃ h) =
      character δ π classes T.obj₁ h₁
          (isDefined_obj₁_of_distinguished δ π T hT h₁ h₂ h₃ h) +
        character δ π classes T.obj₃ h₃
          (isDefined_obj₃_of_distinguished δ π T hT h₁ h₂ h₃ h) := sorry

/-- Every Newton class adds along a distinguished triangle of perfect derived modules under
the envelope representability, direct representability, or quasi-compactness alternatives. -/
theorem newtonClass_distinguished
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π] (classes : Theory δ π)
    (T : Triangle (RingedSpace.ModuleDerived X.toRingedSpace))
    (hT : T ∈ distTriang (RingedSpace.ModuleDerived X.toRingedSpace))
    (h₁ : RingedSpace.ModuleDerived.IsPerfect T.obj₁)
    (h₂ : RingedSpace.ModuleDerived.IsPerfect T.obj₂)
    (h₃ : RingedSpace.ModuleDerived.IsPerfect T.obj₃)
    (h : (∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsEnvelope f ∧
        HasLocallyBoundedFiniteLocallyFree
          ((RingedSpace.modulePullbackDerived f.toShHom).map T.mor₁)) ∨
      HasLocallyBoundedFiniteLocallyFree T.mor₁ ∨
      (∀ Z : irreducibleComponents X, IsCompact (Z : Set X)) ∨ CompactSpace X)
    (p : ℕ) :
    newtonClass δ π classes T.obj₂ h₂
        (isDefined_obj₂_of_distinguished δ π T hT h₁ h₂ h₃ h) p =
      newtonClass δ π classes T.obj₁ h₁
          (isDefined_obj₁_of_distinguished δ π T hT h₁ h₂ h₃ h) p +
        newtonClass δ π classes T.obj₃ h₃
          (isDefined_obj₃_of_distinguished δ π T hT h₁ h₂ h₃ h) p := sorry

end AlgebraicGeometry.ChernClass.Derived
