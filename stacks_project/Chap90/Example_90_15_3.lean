/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Finite.Defs
public import stacks_project.Chap90.Example_90_15_3_Quotient
public import stacks_project.Chap90.Example_90_15_3_FrobeniusShear
public import stacks_project.Chap90.«90_15_0_2»

/-!
# Quotient of restricted coyoneda of dual numbers by a finite automorphism group

The orbit quotient `F = underline{k[ε]}/G` is a predeformation category with a
versal formal object, but it fails Schlessinger's condition
(S2) when `G` is finite and nontrivial. The quotient map is smooth, and the
tangent space of `F` is the `G`-orbit quotient of `Hom(k[ε], k[ε])`.

The source's unconditional assertion of 90.15.0.2 needs an erratum: the
differential is bijective on derivation-orbits exactly when every element of
`G` has infinitesimal scaling coefficient one. No restriction on `G` is imposed
in the corrected equivalence below.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat
open scoped BasedFunctor

universe u

section
variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (G : Subgroup (Aut (dualNumber Λ k)))

/-- Example 90.15.3 (1): the orbit quotient `F = underline{k[ε]}/G` is a
predeformation category. -/
@[stacks 06T7, instance]
instance instIsPredeformationCategory_quotientProjection :
    Functor.IsPredeformationCategory (quotientProjection G) := sorry

/-- Example 90.15.3 (2): the image of the identity formal object of
`underline{k[ε]}` is a versal formal object of `F`. -/
@[stacks 06T7, instance]
instance instIsVersal_quotientFormalObject :
    FormalObject.IsVersal (quotientFormalObject G) := sorry

/-- Example 90.15.3 (3), corrected: the versal formal object of `F = underline{k[ε]}/G`
satisfies 90.15.0.2 if and only if every element of `G` acts trivially on the
one-dimensional square-zero ideal. -/
@[stacks 06T7]
theorem bijectiveDifferentialOnOrbits_quotientFormalObject :
    FormalObject.BijectiveDifferentialOnOrbits (quotientFormalObject G) ↔
      ∀ g : G, epsilonScale g.val = 1 := sorry

/-- Example 90.15.3 (4): if `G` is finite and nontrivial, then `F` does not
satisfy (S2). -/
@[stacks 06T7]
theorem not_hasSchlessingerS2_quotientProjection [Finite G] (h_nontrivial : G ≠ ⊥) :
    ¬ Functor.HasSchlessingerS2 (quotientProjection G) := sorry

/-- Example 90.15.3 (5): the quotient map `underline{k[ε]} ⟶ F` is smooth. -/
@[stacks 06T7, instance]
instance instIsSmooth_quotientBasedFunctor :
    BasedFunctor.IsSmooth (quotientBasedFunctor G) := sorry

/-- The comparison from `G`-orbits on `underline{k[ε]}(k[ε])` to the tangent space of
`F`. -/
noncomputable def tangentSpaceMkQuot (q : Quot (orbitRel G (dualNumber Λ k))) :
    Functor.tangentSpace (quotientProjection G) :=
  Functor.tangentSpace.mk (quotientProjection G)
    (Functor.Fiber.mk
      (rfl : (quotientProjection G).obj (orbitQuotientElement G q) = dualNumber Λ k))

/-- The comparison `tangentSpaceMkQuot` evaluates as the isomorphism class of the
dual-number fibre object with component `q`. -/
theorem tangentSpaceMkQuot_eq (q : Quot (orbitRel G (dualNumber Λ k))) :
    tangentSpaceMkQuot G q =
      Functor.tangentSpace.mk (quotientProjection G)
        (Functor.Fiber.mk
          (rfl : (quotientProjection G).obj (orbitQuotientElement G q) =
            dualNumber Λ k)) := sorry

/-- The differential of the pushed identity formal object is the tangent class of
the actual dual-number point associated to the derivation, followed by the quotient. -/
theorem differential_quotientFormalObject
    (D : Derivation Λ (dualNumberComplete Λ k).carrier k) :
    FormalObject.differential (quotientFormalObject G) D =
      tangentSpaceMkQuot G
        (Quot.mk (orbitRel G (dualNumber Λ k)) (dualNumberPointOfDerivation D)) := sorry

/-- Two tangent images of the quotient formal object have the same residue-derivation
orbit exactly when their infinitesimal coefficients differ by a scaling from `G`. -/
theorem differential_orbit_iff_epsilonScale
    (D₁ D₂ : Derivation Λ (dualNumberComplete Λ k).carrier k) :
    FormalObject.differential (quotientFormalObject G) D₁ ∈
        AddAction.orbit (Derivation Λ k k)
          (FormalObject.differential (quotientFormalObject G) D₂) ↔
      ∃ g : G, D₁ (TrivSqZeroExt.inr (1 : k)) =
        epsilonScale g.val * D₂ (TrivSqZeroExt.inr (1 : k)) := sorry

/-- Example 90.15.3 (6): the tangent space of `F` is the `G`-orbit quotient of
`underline{k[ε]}(k[ε])`. -/
@[stacks 06T7]
theorem tangentSpace_quotientBy [Finite G] :
    Function.Bijective (tangentSpaceMkQuot G) := sorry

end

namespace ArtinianLocalAlgCat.FrobeniusShear

/-- Example 90.15.3 (7): the explicit Frobenius shear group on `k = F₂(t)` yields a
formal object of `underline{k[ε]}/G` satisfying 90.15.0.2. -/
@[stacks 06T7]
theorem bijectiveDifferentialOnOrbits :
    FormalObject.BijectiveDifferentialOnOrbits (quotientFormalObject shearGroup) := sorry

end ArtinianLocalAlgCat.FrobeniusShear
