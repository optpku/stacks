/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import stacks_project.Chap90.Lemma_90_12_2_Tensor
public import stacks_project.Chap90.Lemma_90_20_1_LinearMap
public import stacks_project.Chap99.Lemma_99_15_8_Predeformation
public import stacks_project.Chap99.Lemma_99_15_8_Tangent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite-dimensional tangent and infinitesimal automorphism spaces

For an object `x` of `𝒳 = Curves` over `Spec(k)`, the Artin spaces
`Tℱ_{𝒳, k, x}` and `Inf(ℱ_{𝒳, k, x})` of Section 98.8 are
finite-dimensional when `k` is of finite type over `S`, and in general the RS*
spaces `T_x(k)` and `Inf_x(k)` of Section 98.21 are finite-dimensional.
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

/-- Lemma 99.15.8 (1): let `k` be a field and let `x = (X ⟶ Spec(k))` be an
object of `𝒳 = Curves` over `Spec(k)`. If `k` is of finite type over `S`
(source: over `Spec(ℤ)`), then the Artin tangent space `Tℱ_{𝒳, k, x}` of
Section 98.8 is a finite-dimensional `k`-vector space. -/
@[stacks 0D57]
theorem finiteDimensional_tangentSpace
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

/-- Lemma 99.15.8 (2): let `k` be a field and let `x = (X ⟶ Spec(k))` be an
object of `𝒳 = Curves` over `Spec(k)`. If `k` is of finite type over `S`
(source: over `Spec(ℤ)`), then the infinitesimal automorphism space
`Inf(ℱ_{𝒳, k, x})` of Section 98.8 is a finite-dimensional `k`-vector space. -/
@[stacks 0D57]
theorem finiteDimensional_infinitesimalAutomorphisms
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

/-- Lemma 99.15.8 (3): let `k` be a field and let `x = (X ⟶ Spec(k))` be an
object of `𝒳 = Curves` over `Spec(k)`. In general the RS* tangent space
`T_x(k)` of Section 98.21 is a finite-dimensional `k`-vector space. -/
@[stacks 0D57]
theorem finiteDimensional_tangentAt {S : Scheme.{u}} {k : Type u} [Field k]
    (kToS : Spec (CommRingCat.of k) ⟶ S)
    (x : (p S).Fiber (Over.mk kToS)) :
    FiniteDimensional k (tangentAt kToS x) :=
  sorry

/-- Lemma 99.15.8 (4): let `k` be a field and let `x = (X ⟶ Spec(k))` be an
object of `𝒳 = Curves` over `Spec(k)`. In general the RS* infinitesimal
automorphism space `Inf_x(k)` of Section 98.21 is a finite-dimensional
`k`-vector space. -/
@[stacks 0D57]
theorem finiteDimensional_infAt {S : Scheme.{u}} {k : Type u} [Field k]
    (kToS : Spec (CommRingCat.of k) ⟶ S)
    (x : (p S).Fiber (Over.mk kToS)) :
    FiniteDimensional k (infAt kToS x) :=
  sorry

end Curves
end AlgebraicGeometry.AlgebraicSpace.Spaces
