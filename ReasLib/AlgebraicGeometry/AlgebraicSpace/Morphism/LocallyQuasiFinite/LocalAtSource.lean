module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtalePrecoverage

/-!
# Local finite-type quasi-finiteness is étale local on the source

The conjunction of being locally of finite type and locally quasi-finite for
morphisms of algebraic spaces is local on the source for the étale precoverage.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FiniteType

/-- The conjunction of being locally of finite type and locally quasi-finite for
morphisms of algebraic spaces is local on the source for the étale precoverage. -/
instance locallyQuasiFiniteIsLocalAtSourceEtale {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtSource
      (@LocallyOfFiniteType S ⊓ @LocallyQuasiFinite S :
        MorphismProperty (AlgebraicSpace S))
      (@etalePrecoverage S) :=
  sorry

/-- A morphism of algebraic spaces is locally of finite type and locally
quasi-finite if and only if its composite with every member of an étale covering
of the source is locally of finite type and locally quasi-finite. -/
theorem locallyQuasiFinite_iff_forall_comp_etale {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (𝒰 : (@etalePrecoverage S).ZeroHypercover X) :
    LocallyOfFiniteType f ∧ LocallyQuasiFinite f ↔
      ∀ i, LocallyOfFiniteType (𝒰.f i ≫ f) ∧ LocallyQuasiFinite (𝒰.f i ≫ f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FiniteType
