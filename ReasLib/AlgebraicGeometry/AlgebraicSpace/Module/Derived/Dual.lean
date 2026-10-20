module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.InternalHom

/-! # Derived structure-sheaf duals on algebraic spaces -/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The derived dual is derived sheaf Hom into the structure sheaf concentrated in degree zero. -/
def dual (P : ModuleDerived X) : ModuleDerived X :=
  InternalHom.obj P ((DerivedCategory.singleFunctor (Modules X) 0).obj (𝟙_ (Modules X)))

/-- A source representative and a K-injective representative of the degree-zero structure
sheaf compute the derived dual, independently of the chosen representatives. -/
theorem dual_model (P : ModuleDerived X) (F I : CochainComplex (Modules X) ℤ)
    [I.IsKInjective] (sourceIso : DerivedCategory.Q.obj F ≅ P)
    (targetIso : DerivedCategory.Q.obj I ≅
      (DerivedCategory.singleFunctor (Modules X) 0).obj (𝟙_ (Modules X))) :
    IsIsomorphic (dual P) (DerivedCategory.Q.obj (InternalHom.complex F I)) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
