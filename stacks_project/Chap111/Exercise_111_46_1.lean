module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NonvanishingLocus
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import stacks_project.Chap111.Exercise_111_39_1_FieldPoint
public import stacks_project.Chap111.Exercise_111_46_1_VanishingLocus

/-!
# Closed points of the tautological vanishing locus

The closed-point characterisation of the incidence subscheme of a linear
system on `ℙ^n ×_k X`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.LinearSystem

/-- Exercise 111.46.1: let `k` be an algebraically closed field, let `X` be a
projective curve over `k`, let `L` be an invertible `𝒪_X`-module, and let
`s 0, …, s n` be global sections of `L`. There is a natural closed subscheme
`Z ⊂ ℙ^n ×_k X`, namely `vanishingIdeal X L n s`, such that a closed point
`((v 0 : … : v n), x)` of the product lies on `Z` if and only if the section
`v 0 • s 0 + ⋯ + v n • s n` vanishes at `x`. -/
@[stacks 0EG9]
theorem closedPoint_mem_vanishingIdeal_iff
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Curve X] [Projective X.hom]
    (L : X.left.Modules) [Scheme.Modules.Invertible L]
    (n : ℕ) (s : Fin (n + 1) → SchemeOverField.globalSectionsMod X L)
    {v : Fin (n + 1) → k} (hv : v ≠ 0)
    {x : X.left} (hx : x ∈ closedPoints X.left)
    {z : product X n} (hz : z ∈ closedPoints (product X n))
    (hfst : fst X n z =
      ProjectiveSpace.homOf (RingHom.id k) hv (IsLocalRing.closedPoint k))
    (hsnd : snd X n z = x) :
    z ∈ (vanishingIdeal X L n s).support ↔
      x ∉ RingedSpace.sectionNonvanishingLocus X.left.toRingedSpace L
        (linearCombination X L n s v) :=
  sorry

end AlgebraicGeometry.LinearSystem
