/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.FiniteDimensional
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CohStack

noncomputable section

universe u

/- Lemma 99.5.9 (1): the tangent space is finite dimensional. -/
@[stacks 08W8] #check (AlgebraicGeometry.AlgebraicSpace.CohStack.finiteDimensional_tangentSpace :
    ∀ {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f]
    [LocallyOfFinitePresentation (SchemeRealization.toBase B)] {Λ k : Type u}
    [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
    [AlgebraicGeometry.IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x0 : (p f).Fiber (Over.mk kToS)),
    FiniteDimensional k (tangentSpace f openImmersion kToS h_factor x0))

/- Lemma 99.5.9 (2): the infinitesimal automorphism space is finite dimensional. -/
@[stacks 08W8] #check (AlgebraicGeometry.AlgebraicSpace.CohStack.finiteDimensional_infinitesimalAutomorphisms :
    ∀ {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f]
    [LocallyOfFinitePresentation (SchemeRealization.toBase B)] {Λ k : Type u}
    [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
    [AlgebraicGeometry.IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x0 : (p f).Fiber (Over.mk kToS)),
    FiniteDimensional k (infinitesimalAutomorphisms f openImmersion kToS h_factor x0))

