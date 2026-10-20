module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Predeformation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Tangent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProper.FiniteDimensional

/-!
# Finite-dimensional deformation spaces of curves

The RS* tangent and infinitesimal spaces of a curve over a field are finite dimensional. The Artin spaces have the
same finiteness property over a locally Noetherian base, with a field finite as
a module over its chosen affine chart and a locally finite-type field point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces
open AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
open ArtinianLocalAlgCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces
namespace Curves

/-- The Artin tangent space of a curve is finite dimensional over a field finite as a module over its chosen
Noetherian affine chart, when the field point is locally of finite type. -/
instance finiteDimensional_tangentSpace
    {S : Scheme.{u}} [IsLocallyNoetherian S] {Λ k : Type u}
    [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
    [AlgebraicGeometry.IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x : (p S).Fiber (Over.mk kToS)) :
    FiniteDimensional k (tangentSpace openImmersion kToS h_factor x) :=
  sorry

/-- The Artin infinitesimal automorphism space of a curve is finite dimensional over a field finite as a module
over its chosen Noetherian affine chart, when the point is locally of finite type. -/
instance finiteDimensional_infinitesimalAutomorphisms
    {S : Scheme.{u}} [IsLocallyNoetherian S] {Λ k : Type u}
    [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
    [AlgebraicGeometry.IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x : (p S).Fiber (Over.mk kToS)) :
    FiniteDimensional k (infinitesimalAutomorphisms openImmersion kToS h_factor x) :=
  sorry

/-- The RS* tangent space of a curve over an arbitrary field is finite dimensional. -/
instance finiteDimensional_tangentAt {S : Scheme.{u}} {k : Type u} [Field k]
    (kToS : Spec (CommRingCat.of k) ⟶ S)
    (x : (p S).Fiber (Over.mk kToS)) :
    FiniteDimensional k (tangentAt kToS x) :=
  sorry

/-- The RS* infinitesimal automorphism space of a curve over an arbitrary field is finite dimensional. -/
instance finiteDimensional_infAt {S : Scheme.{u}} {k : Type u} [Field k]
    (kToS : Spec (CommRingCat.of k) ⟶ S)
    (x : (p S).Fiber (Over.mk kToS)) :
    FiniteDimensional k (infAt kToS x) :=
  sorry

end Curves
end AlgebraicGeometry.AlgebraicSpace.Spaces
