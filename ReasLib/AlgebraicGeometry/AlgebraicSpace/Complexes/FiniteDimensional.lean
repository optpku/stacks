/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Complexes.Predeformation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization

/-!
# Finite-dimensional deformation spaces of relatively perfect complexes

The tangent and infinitesimal automorphism spaces at a finite-type field-valued
relatively perfect complex with vanishing negative fibre self-Ext are finite dimensional.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Complexes

/-- For a proper, flat morphism of finite presentation over a locally Noetherian
scheme, with locally finitely presented base space, the tangent space at a
finite-type field-valued relatively perfect complex with vanishing negative fibre
self-Ext is finite dimensional over the field, presented as finite over a
Noetherian affine chart. -/
instance finiteDimensional_tangentSpace
    {S : Scheme.{u}} [IsLocallyNoetherian S] {X B : AlgebraicSpace S}
    (f : X ⟶ B) [Proper f] [Flat f] [FinitePresentation f]
    [LocallyOfFinitePresentation (SchemeRealization.toBase B)] {Λ k : Type u}
    [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
    [AlgebraicGeometry.IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x0 : (p f).Fiber (Over.mk kToS)) :
    FiniteDimensional k (tangentSpace f openImmersion kToS h_factor x0) := sorry

/-- For a proper, flat morphism of finite presentation over a locally Noetherian
scheme, with locally finitely presented base space, the infinitesimal automorphism space at a
finite-type field-valued relatively perfect complex with vanishing negative fibre
self-Ext is finite dimensional over the field, presented as finite over a
Noetherian affine chart. -/
instance finiteDimensional_infinitesimalAutomorphisms
    {S : Scheme.{u}} [IsLocallyNoetherian S] {X B : AlgebraicSpace S}
    (f : X ⟶ B) [Proper f] [Flat f] [FinitePresentation f]
    [LocallyOfFinitePresentation (SchemeRealization.toBase B)] {Λ k : Type u}
    [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
    [AlgebraicGeometry.IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x0 : (p f).Fiber (Over.mk kToS)) :
    FiniteDimensional k (infinitesimalAutomorphisms f openImmersion kToS h_factor x0) := sorry

end AlgebraicGeometry.AlgebraicSpace.Complexes
