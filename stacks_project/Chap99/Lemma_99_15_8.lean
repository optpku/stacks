/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.FiniteDimensional
import StacksCheckRecall

/-!
# Finite-dimensional deformation spaces of curves

The Artin tangent and infinitesimal automorphism spaces are finite dimensional
for fields of finite type over ℤ, expressed here with explicit finite-module
affine-chart hypotheses. The RS* spaces are finite dimensional over every field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

universe u

/- Lemma 99.15.8 (1): the Artin tangent space is finite dimensional under the finite-module affine-chart hypotheses. -/
@[stacks 0D57] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.finiteDimensional_tangentSpace :
    ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {Λ k : Type u}
    [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
    [AlgebraicGeometry.IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x : (p S).Fiber (Over.mk kToS)),
    FiniteDimensional k (tangentSpace openImmersion kToS h_factor x))

/- Lemma 99.15.8 (2): the Artin infinitesimal automorphism space is finite dimensional under the same hypotheses. -/
@[stacks 0D57] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.finiteDimensional_infinitesimalAutomorphisms :
    ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {Λ k : Type u}
    [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
    [AlgebraicGeometry.IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x : (p S).Fiber (Over.mk kToS)),
    FiniteDimensional k (infinitesimalAutomorphisms openImmersion kToS h_factor x))

/- Lemma 99.15.8 (3): the RS* tangent space is finite dimensional over an arbitrary field. -/
@[stacks 0D57] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.finiteDimensional_tangentAt :
    ∀ {S : Scheme.{u}} {k : Type u} [Field k]
    (kToS : Spec (CommRingCat.of k) ⟶ S)
    (x : (p S).Fiber (Over.mk kToS)),
    FiniteDimensional k (tangentAt kToS x))

/- Lemma 99.15.8 (4): the RS* infinitesimal automorphism space is finite dimensional over an arbitrary field. -/
@[stacks 0D57] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.finiteDimensional_infAt :
    ∀ {S : Scheme.{u}} {k : Type u} [Field k]
    (kToS : Spec (CommRingCat.of k) ⟶ S)
    (x : (p S).Fiber (Over.mk kToS)),
    FiniteDimensional k (infAt kToS x))
