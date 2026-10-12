/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap90.Lemma_90_12_2_Tensor
public import stacks_project.Chap90.Lemma_90_20_1_LinearMap
public import stacks_project.Chap99.Lemma_99_5_9_Predeformation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite-dimensional tangent and infinitesimal automorphism spaces of `Coh_{X/B}`

In Situation 99.5.1, if `S` is locally Noetherian and `B → S` is locally of
finite presentation, then for every finite-type field `k` over `S` and every
object `x0` of `Coh_{X/B}` over `k`, the Artin-axiom spaces
`Tℱ_{𝒳, k, x0}` and `Inf(ℱ_{𝒳, k, x0})` are finite-dimensional `k`-vector
spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CohStack ArtinianLocalAlgCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

/-- Lemma 99.5.9 (1): in Situation 99.5.1 assume that `S` is locally Noetherian
and `toBase B` is locally of finite presentation. Let `k` be a finite type field
over `S` and let `x0` be an object of `𝒳 = Coh_{X/B}` over `k`. Then the
tangent space `Tℱ_{𝒳, k, x0}`, the isomorphism classes of the fibre of
`predeformation f openImmersion kToS h_factor x0` over `dualNumber Λ k`, is
finite-dimensional over `k`. -/
@[stacks 08W8]
theorem finiteDimensional_tangentSpace
    {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f]
    [LocallyOfFinitePresentation (toBase B)] {Λ k : Type u}
    [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
    [AlgebraicGeometry.IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x0 : (p f).Fiber (Over.mk kToS)) :
    FiniteDimensional k ((Functor.fiberIsoClassFunctor
        (predeformation f openImmersion kToS h_factor x0)).obj
      (dualNumber Λ k)) :=
  sorry

/-- Lemma 99.5.9 (2): in Situation 99.5.1 assume that `S` is locally Noetherian
and `toBase B` is locally of finite presentation. Let `k` be a finite type field
over `S` and let `x0` be an object of `𝒳 = Coh_{X/B}` over `k`. Then the
infinitesimal automorphism space `Inf(ℱ_{𝒳, k, x0}) :=
Functor.infinitesimalAutomorphisms (predeformation f openImmersion kToS
h_factor x0)` is finite-dimensional over `k`. -/
@[stacks 08W8]
theorem finiteDimensional_infinitesimalAutomorphisms
    {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f]
    [LocallyOfFinitePresentation (toBase B)] {Λ k : Type u}
    [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
    [AlgebraicGeometry.IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x0 : (p f).Fiber (Over.mk kToS)) :
    FiniteDimensional k (Functor.infinitesimalAutomorphisms
      (predeformation f openImmersion kToS h_factor x0)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
