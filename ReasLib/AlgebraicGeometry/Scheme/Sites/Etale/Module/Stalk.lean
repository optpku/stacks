module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.RingTheory.Flat.Basic

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

/-- The geometric stalk complex of an étale module sheaf complex is obtained by applying the
canonical geometric fiber functor to its terms and differentials. -/
def moduleStalkComplex {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (geometricPoint : Spec (.of Ω) ⟶ X)
    (K : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ) :
    CochainComplex (ModuleCat.{u} Λ) ℤ :=
  ((Scheme.pointSmallEtale geometricPoint).sheafFiber.mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K

/-- An étale module sheaf is stalkwise flat if its canonical fiber at every algebraically
closed field-valued geometric point is a flat module. -/
def IsStalkwiseFlatModule (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (geometricPoint : Spec (.of Ω) ⟶ X),
    Module.Flat Λ
      (((Scheme.pointSmallEtale geometricPoint).sheafFiber (A := ModuleCat.{u} Λ)).obj F)

end AlgebraicGeometry.Scheme.Etale
