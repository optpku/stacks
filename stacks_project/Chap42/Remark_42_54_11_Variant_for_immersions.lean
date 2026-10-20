/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.VirtualNormalBundle
public import ReasLib.AlgebraicGeometry.BivariantClass.VirtualNormalBundle

open AlgebraicGeometry CategoryTheory

universe u

/- Remark 42.54.11 (Variant for immersions): a virtual normal bundle records an explicit
finite locally free module and a quotient of its dual onto the conormal sheaf. -/
@[stacks 0FBQ] #check (AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle :
  ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i], Type (u + 1))

/- The completed bivariant class is independent
of the chosen factorization as a closed immersion followed by an open immersion. -/
#check (AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle.bivariantClass_eq_ofFactorization :
    ∀ {S Z U X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
      [IsDimensionFunction delta]
      (closedClass : AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle.ClosedVirtualNormalClass
        S delta)
      (h_closed : AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle.RespectsOpenRestriction
        delta closedClass)
      (p : X ⟶ S) [LocallyOfFiniteType p] (i : Z ⟶ X) [IsImmersion i]
      (V : AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle i)
      (j : Z ⟶ U) (k : U ⟶ X) [IsClosedImmersion j] [IsOpenImmersion k]
      (h : j ≫ k = i),
        AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle.bivariantClass
            delta closedClass p i V =
          AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle.composeClasses
            delta (i ≫ p) p i rfl j k h V
              (closedClass (i ≫ p) (k ≫ p) j
                (AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle.factorization_over
                  (i ≫ p) p i rfl j k h)
                (AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle.forFactorization
                  i j k h V)))
