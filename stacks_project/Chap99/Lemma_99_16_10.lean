/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Complexes.FiniteDimensional
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Complexes

noncomputable section

universe u

/- Lemma 99.16.10 (1): in Situation 99.16.3, if `S` is locally Noetherian and
`B ⟶ S` is locally of finite presentation, the tangent space at a finite-type
field-valued object is finite dimensional. -/
@[stacks 0DLL] #check (AlgebraicGeometry.AlgebraicSpace.Complexes.finiteDimensional_tangentSpace :
    ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X B : AlgebraicSpace S}
    (f : X ⟶ B) [Proper f] [Flat f] [FinitePresentation f]
    [LocallyOfFinitePresentation (SchemeRealization.toBase B)] {Λ k : Type u}
    [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
    [AlgebraicGeometry.IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x0 : (p f).Fiber (Over.mk kToS)),
    FiniteDimensional k (tangentSpace f openImmersion kToS h_factor x0))

/- Lemma 99.16.10 (2): in Situation 99.16.3, if `S` is locally Noetherian and
`B ⟶ S` is locally of finite presentation, the infinitesimal automorphism space at a finite-type
field-valued object is finite dimensional. -/
@[stacks 0DLL] #check (AlgebraicGeometry.AlgebraicSpace.Complexes.finiteDimensional_infinitesimalAutomorphisms :
    ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X B : AlgebraicSpace S}
    (f : X ⟶ B) [Proper f] [Flat f] [FinitePresentation f]
    [LocallyOfFinitePresentation (SchemeRealization.toBase B)] {Λ k : Type u}
    [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
    [AlgebraicGeometry.IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x0 : (p f).Fiber (Over.mk kToS)),
    FiniteDimensional k (infinitesimalAutomorphisms f openImmersion kToS h_factor x0))

