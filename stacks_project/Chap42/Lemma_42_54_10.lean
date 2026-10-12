/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap42.Lemma_42_54_2_BivariantClass
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.Transitivity

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Hom
namespace VirtualNormalBundle

open Hom.Conormal.Transitivity

/-- Nested closed immersions `Z ⟶ Y` and `Y ⟶ X` compose as morphisms over `S`. -/
theorem overHom_comp {S Z Y X : Scheme.{u}} (p : X ⟶ S) (j : Y ⟶ X) (i : Z ⟶ Y) :
    overHom (i ≫ j ≫ p) (j ≫ p) i rfl ≫ overHom (j ≫ p) p j rfl =
      overHom (i ≫ j ≫ p) p (i ≫ j) rfl := sorry

/-- The degree-`n` convolution of the virtual-normal classes of `Z ⟶ Y` and `Y ⟶ X`. -/
noncomputable def globalClassConvolution
    {S Z Y X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (p : X ⟶ S) [LocallyOfFiniteType p]
    (j : Y ⟶ X) [IsClosedImmersion j] [LocallyOfFiniteType (j ≫ p)]
    (i : Z ⟶ Y) [IsClosedImmersion i] [LocallyOfFiniteType (i ≫ j ≫ p)]
    (V' : VirtualNormalBundle i)
    (D' : ClosedSpecialization delta (i ≫ j ≫ p) (j ≫ p) i rfl V')
    (V'' : VirtualNormalBundle j)
    (D'' : ClosedSpecialization delta (j ≫ p) p j rfl V'') (n : ℕ) :
    BivariantClass.Nonnegative delta
      (overHom (i ≫ j ≫ p) (j ≫ p) i rfl ≫ overHom (j ≫ p) p j rfl) :=
  -- Local instance justification (defeq pin): Finset.sum needs the named pointwise AddCommGroup of BivariantClass, which Composition.lean exposes as pointwiseAddCommGroup rather than a global instance.
  letI := BivariantClass.pointwiseAddCommGroup delta
    (overHom (i ≫ j ≫ p) (j ≫ p) i rfl ≫ overHom (j ≫ p) p j rfl) (n : ℤ)
  DirectSum.of
    (fun k : ℕ ↦ BivariantClass delta
      (overHom (i ≫ j ≫ p) (j ≫ p) i rfl ≫ overHom (j ≫ p) p j rfl) (k : ℤ))
    n
    (∑ ij : Finset.antidiagonal n,
      BivariantClass.Nonnegative.castGrading delta
        (BivariantClass.Nonnegative.antidiagonalDegree n ij)
        (BivariantClass.comp delta
          (overHom (i ≫ j ≫ p) (j ≫ p) i rfl) (overHom (j ≫ p) p j rfl)
          (globalClassOfRank delta (i ≫ j ≫ p) (j ≫ p) i rfl V' D' ij.1.1)
          (globalClassOfRank delta (j ≫ p) p j rfl V'' D'' ij.1.2)))

/-- Degree `n` of the nested virtual-normal convolution is its finite antidiagonal sum. -/
theorem globalClassConvolution_apply
    {S Z Y X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (p : X ⟶ S) [LocallyOfFiniteType p]
    (j : Y ⟶ X) [IsClosedImmersion j] [LocallyOfFiniteType (j ≫ p)]
    (i : Z ⟶ Y) [IsClosedImmersion i] [LocallyOfFiniteType (i ≫ j ≫ p)]
    (V' : VirtualNormalBundle i)
    (D' : ClosedSpecialization delta (i ≫ j ≫ p) (j ≫ p) i rfl V')
    (V'' : VirtualNormalBundle j)
    (D'' : ClosedSpecialization delta (j ≫ p) p j rfl V'') (n : ℕ) :
    globalClassConvolution delta p j i V' D' V'' D'' n n =
      @Finset.sum
        {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal n}
        (BivariantClass delta
          (overHom (i ≫ j ≫ p) (j ≫ p) i rfl ≫ overHom (j ≫ p) p j rfl) (n : ℤ))
        (BivariantClass.pointwiseAddCommGroup delta
          (overHom (i ≫ j ≫ p) (j ≫ p) i rfl ≫ overHom (j ≫ p) p j rfl)
          (n : ℤ)).toAddCommMonoid
        Finset.univ
        (fun ij ↦
          BivariantClass.Nonnegative.castGrading delta
            (BivariantClass.Nonnegative.antidiagonalDegree n ij)
            (BivariantClass.comp delta
              (overHom (i ≫ j ≫ p) (j ≫ p) i rfl) (overHom (j ≫ p) p j rfl)
              (globalClassOfRank delta (i ≫ j ≫ p) (j ≫ p) i rfl V' D' ij.1.1)
              (globalClassOfRank delta (j ≫ p) p j rfl V'' D'' ij.1.2))) := sorry

/-- Lemma 42.54.10: for nested closed subschemes `Z ⊂ Y ⊂ X` locally of finite type over
Situation 42.7.1, with virtual normal sheaves `N`, `N'`, `N''` for `Z ⟶ X`, `Z ⟶ Y`,
`Y ⟶ X`, if the duals fit in a commutative diagram whose top row is a short exact
sequence and whose bottom row is the conormal transitivity sequence
`i^* C_{Y/X} ⟶ C_{Z/X} ⟶ C_{Z/Y}`, then `c(Z ⟶ X, N) = c(Z ⟶ Y, N') ∘ c(Y ⟶ X, N'')`
in `A^*(Z ⟶ X)^∧`. -/
@[stacks 0FEC]
theorem closedClass_comp
    {S Z Y X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (p : X ⟶ S) [LocallyOfFiniteType p]
    (j : Y ⟶ X) [IsClosedImmersion j] [LocallyOfFiniteType (j ≫ p)]
    (i : Z ⟶ Y) [IsClosedImmersion i] [LocallyOfFiniteType (i ≫ j ≫ p)]
    (V : VirtualNormalBundle (i ≫ j))
    (D : ClosedSpecialization delta (i ≫ j ≫ p) p (i ≫ j) rfl V)
    (V' : VirtualNormalBundle i)
    (D' : ClosedSpecialization delta (i ≫ j ≫ p) (j ≫ p) i rfl V')
    (V'' : VirtualNormalBundle j)
    (D'' : ClosedSpecialization delta (j ≫ p) p j rfl V'')
    (incl :
      (Scheme.Modules.pullback i).obj (Scheme.Modules.dual V''.module) ⟶
        Scheme.Modules.dual V.module)
    (proj : Scheme.Modules.dual V.module ⟶ Scheme.Modules.dual V'.module)
    (hzero : incl ≫ proj = 0) (hshort : (ShortComplex.mk incl proj hzero).ShortExact)
    (h_left :
      CommSq incl ((Scheme.Modules.pullback i).map V''.map) V.map
        (baseChange i j))
    (h_right :
      CommSq proj V.map V'.map (projection i j))
    (n : ℕ) :
    BivariantClass.Nonnegative.castHom delta (overHom_comp p j i)
        (globalClassConvolution delta p j i V' D' V'' D'' n) n =
      globalClassOfRank delta (i ≫ j ≫ p) p (i ≫ j) rfl V D n := sorry

end VirtualNormalBundle
end Hom
end Scheme
end AlgebraicGeometry

