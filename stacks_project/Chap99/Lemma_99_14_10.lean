/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import ReasLib.RingTheory.Noetherian.ULift
public import stacks_project.Chap90.Lemma_90_20_1_LinearMap
public import stacks_project.Chap98.«98_3_0_2»
public import stacks_project.Chap98.«98_8_0_1_TangentSpace»
public import stacks_project.Chap98.Lemma_98_21_2_Functor
public import stacks_project.Chap98.Remark_98_6_2
public import stacks_project.Chap98.Remark_98_21_7_Compatibility_with_previous_tangent_spaces_Comparison
public import stacks_project.Chap99.Lemma_99_14_8_Groupoids
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite-dimensional tangent and infinitesimal automorphism spaces of Polarized

For an object `x = (X ⟶ Spec(k), L)` of `𝒳 = Polarized` over `Spec(k)`, the
Artin spaces `Tℱ_{𝒳, k, x}` and `Inf(ℱ_{𝒳, k, x})` of Section 98.8 are
finite-dimensional when `k` is of finite type over `ℤ`, and in general the RS*
spaces `T_x(k)` and `Inf_x(k)` of Section 98.21 are finite-dimensional.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupoidsOver
open AlgebraicGeometry.GroupoidsOver.Predeformation
open ArtinianLocalAlgCat

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

/-- Polarized over `specZ` satisfies the strong Rim-Schlessinger condition (RS*). -/
instance instHasStrongRimSchlessinger :
    HasStrongRimSchlessinger toGroupoidsOverSpecZ :=
  sorry

/-- The predeformation functor of a Polarized residue object satisfies the
Rim-Schlessinger condition (RS). -/
instance instHasRimSchlessinger_predeformationFunctor
    {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] (openImmersion : Spec (CommRingCat.of Λ) ⟶ specZ)
    [IsOpenImmersion openImmersion] (kToS : Spec (CommRingCat.of k) ⟶ specZ)
    [LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x : toGroupoidsOverSpecZ.p.Fiber (Over.mk kToS)) :
    Functor.HasRimSchlessinger
      (predeformationFunctor toGroupoidsOverSpecZ openImmersion kToS h_factor x) :=
  sorry

/-- Lemma 99.14.10 (1): let `k` be a field and let `x = (X ⟶ Spec(k), L)` be an
object of `𝒳 = Polarized` over `Spec(k)`. If `k` is of finite type over `ℤ`,
then the Artin tangent space `Tℱ_{𝒳, k, x}` of Section 98.8 is a
finite-dimensional `k`-vector space. -/
@[stacks 0D4S]
theorem finiteDimensional_tangentSpace
    {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] (openImmersion : Spec (CommRingCat.of Λ) ⟶ specZ)
    [IsOpenImmersion openImmersion] (kToS : Spec (CommRingCat.of k) ⟶ specZ)
    [LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x : toGroupoidsOverSpecZ.p.Fiber (Over.mk kToS)) :
    FiniteDimensional k
      (tangentSpace openImmersion kToS h_factor toGroupoidsOverSpecZ x) :=
  sorry

/-- Lemma 99.14.10 (2): let `k` be a field and let `x = (X ⟶ Spec(k), L)` be an
object of `𝒳 = Polarized` over `Spec(k)`. If `k` is of finite type over `ℤ`,
then the infinitesimal automorphism space `Inf(ℱ_{𝒳, k, x})` of Section 98.8
is a finite-dimensional `k`-vector space. -/
@[stacks 0D4S]
theorem finiteDimensional_infinitesimalAutomorphisms
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

/-- Lemma 99.14.10 (3): let `k` be a field and let `x = (X ⟶ Spec(k), L)` be an
object of `𝒳 = Polarized` over `Spec(k)`. In general the RS* tangent space
`T_x(k)` of Section 98.21 is a finite-dimensional `k`-vector space. -/
@[stacks 0D4S]
theorem finiteDimensional_tangentAt {k : Type u} [Field k]
    (kToS : Spec (CommRingCat.of k) ⟶ specZ)
    (x : toGroupoidsOverSpecZ.p.Fiber (Over.mk kToS)) :
    FiniteDimensional k ((tangentFunctor x).obj (ModuleCat.of k k)) :=
  sorry

/-- Lemma 99.14.10 (4): let `k` be a field and let `x = (X ⟶ Spec(k), L)` be an
object of `𝒳 = Polarized` over `Spec(k)`. In general the RS* infinitesimal
automorphism space `Inf_x(k)` of Section 98.21 is a finite-dimensional
`k`-vector space. -/
@[stacks 0D4S]
theorem finiteDimensional_infAt {k : Type u} [Field k]
    (kToS : Spec (CommRingCat.of k) ⟶ specZ)
    (x : toGroupoidsOverSpecZ.p.Fiber (Over.mk kToS)) :
    FiniteDimensional k ((infFunctor x).obj (ModuleCat.of k k)) :=
  sorry

end AlgebraicGeometry.Polarized
