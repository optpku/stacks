/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace.Tensor
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger.FiberIsoClass
public import ReasLib.AlgebraicGeometry.FormalDeformation.RimSchlessinger.Schlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.Unpointed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProper.Predeformation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProper.Tangent

/-!
# Finite-dimensional deformation spaces of proper flat algebraic spaces

The RS* tangent and infinitesimal spaces of a finite-presentation, flat, proper
algebraic space over a field are finite dimensional. The Artin spaces have the
same finiteness property over a locally Noetherian base, with a field finite as
a module over its chosen affine chart and a locally finite-type field point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces
open AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids
open ArtinianLocalAlgCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces
namespace FpFlatProperGroupoids

/-- The Artin tangent space of a finite-presentation, flat, proper algebraic
space is finite dimensional over a field finite as a module over its chosen
Noetherian affine chart, when the field point is locally of finite type. -/
instance finiteDimensional_tangentSpace
    {S : Scheme.{u}} [IsLocallyNoetherian S] {Λ k : Type u}
    [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
    [AlgebraicGeometry.IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x : (pFpFlatProperGroupoids S).Fiber (Over.mk kToS)) :
    FiniteDimensional k (tangentSpace openImmersion kToS h_factor x) :=
  sorry

/-- The Artin infinitesimal automorphism space of a finite-presentation, flat,
proper algebraic space is finite dimensional over a field finite as a module
over its chosen Noetherian affine chart, when the point is locally of finite type. -/
instance finiteDimensional_infinitesimalAutomorphisms
    {S : Scheme.{u}} [IsLocallyNoetherian S] {Λ k : Type u}
    [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
    [AlgebraicGeometry.IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x : (pFpFlatProperGroupoids S).Fiber (Over.mk kToS)) :
    FiniteDimensional k (infinitesimalAutomorphisms openImmersion kToS h_factor x) :=
  sorry

/-- The RS* tangent space of a finite-presentation, flat, proper algebraic
space over an arbitrary field is finite dimensional. -/
instance finiteDimensional_tangentAt {S : Scheme.{u}} {k : Type u} [Field k]
    (kToS : Spec (CommRingCat.of k) ⟶ S)
    (x : (pFpFlatProperGroupoids S).Fiber (Over.mk kToS)) :
    FiniteDimensional k (tangentAt kToS x) :=
  sorry

/-- The RS* infinitesimal automorphism space of a finite-presentation, flat,
proper algebraic space over an arbitrary field is finite dimensional. -/
instance finiteDimensional_infAt {S : Scheme.{u}} {k : Type u} [Field k]
    (kToS : Spec (CommRingCat.of k) ⟶ S)
    (x : (pFpFlatProperGroupoids S).Fiber (Over.mk kToS)) :
    FiniteDimensional k (infAt kToS x) :=
  sorry

end FpFlatProperGroupoids
end AlgebraicGeometry.AlgebraicSpace.Spaces
