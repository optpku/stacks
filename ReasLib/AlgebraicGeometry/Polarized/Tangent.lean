module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import ReasLib.AlgebraicGeometry.Polarized.RimSchlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace.Tensor
public import ReasLib.AlgebraicGeometry.FormalDeformation.RimSchlessinger.Schlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger.FiberIsoClass
public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.Unpointed
public import ReasLib.AlgebraicGeometry.GroupoidsOver.InfinitesimalDeformation
public import ReasLib.AlgebraicGeometry.GroupoidsOver.PredeformationComparison

/-!
# Finite-dimensional deformation spaces of polarized proper schemes

The Artin tangent and infinitesimal automorphism spaces at finite-type field
points are finite dimensional. The geometric tangent and infinitesimal
automorphism spaces are finite dimensional over arbitrary fields.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupoidsOver
open AlgebraicGeometry.GroupoidsOver.Predeformation
open ArtinianLocalAlgCat

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

/-- The Artin tangent space of a polarized proper scheme at a locally finite-type
field point is finite dimensional when the field is finite as a module over
its chosen Noetherian affine chart. -/
@[stacks 0D4S]
instance finiteDimensional_tangentSpace
    {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] (openImmersion : Spec (CommRingCat.of Λ) ⟶ specZ)
    [IsOpenImmersion openImmersion] (kToS : Spec (CommRingCat.of k) ⟶ specZ)
    [LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x : toGroupoidsOverSpecZ.p.Fiber (Over.mk kToS)) :
    FiniteDimensional k
      (CategoryTheory.Functor.tangentSpace
        (predeformationFunctor toGroupoidsOverSpecZ openImmersion kToS h_factor x)) :=
  sorry

/-- The Artin infinitesimal automorphism space of a polarized proper scheme at a
locally finite-type field point is finite dimensional when the field is finite
as a module over its chosen Noetherian affine chart. -/
@[stacks 0D4S]
instance finiteDimensional_infinitesimalAutomorphisms
    {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] (openImmersion : Spec (CommRingCat.of Λ) ⟶ specZ)
    [IsOpenImmersion openImmersion] (kToS : Spec (CommRingCat.of k) ⟶ specZ)
    [LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x : toGroupoidsOverSpecZ.p.Fiber (Over.mk kToS)) :
    FiniteDimensional k
      (Functor.infinitesimalAutomorphisms
        (predeformationFunctor toGroupoidsOverSpecZ openImmersion kToS h_factor x)) :=
  sorry

/-- The geometric tangent space of a polarized proper scheme over an arbitrary
field is finite dimensional. -/
@[stacks 0D4S]
instance finiteDimensional_tangentAt {k : Type u} [Field k]
    (kToS : Spec (CommRingCat.of k) ⟶ specZ)
    (x : toGroupoidsOverSpecZ.p.Fiber (Over.mk kToS)) :
    FiniteDimensional k ((tangentFunctor x).obj (ModuleCat.of k k)) :=
  sorry

/-- The geometric infinitesimal automorphism space of a polarized proper scheme
over an arbitrary field is finite dimensional. -/
@[stacks 0D4S]
instance finiteDimensional_infAt {k : Type u} [Field k]
    (kToS : Spec (CommRingCat.of k) ⟶ specZ)
    (x : toGroupoidsOverSpecZ.p.Fiber (Over.mk kToS)) :
    FiniteDimensional k ((infFunctor x).obj (ModuleCat.of k k)) :=
  sorry

end AlgebraicGeometry.Polarized
