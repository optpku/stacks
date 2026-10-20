/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.Galois
public import ReasLib.FieldTheory.Galois.Closure
public import Mathlib.CategoryTheory.Galois.IsFundamentalgroup

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.GeometricPoint
open scoped FintypeCatDiscrete

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Etale

/-- The slice compatibility equation needed to form the precomposition action on a geometric
fiber. -/
theorem galoisAlgClosure_smul_fac {K Kbar : Type u}
    [Field K] [Field Kbar] [Algebra K Kbar] [IsAlgClosed Kbar]
    {Y : Scheme.FiniteEtale (Spec (.of K))}
    (σ : Gal(Kbar/K))
    (ybar : ((specFieldGeometricPoint K Kbar).finiteFiber).obj Y) :
    (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ ybar.left) ≫ Y.hom =
      (specFieldGeometricPoint K Kbar).hom := sorry

/-- Precomposition by a field automorphism acts on the finite geometric fiber of a finite étale
scheme over a field. -/
def galoisAlgClosure_smul {K Kbar : Type u}
    [Field K] [Field Kbar] [Algebra K Kbar] [IsAlgClosed Kbar]
    {Y : Scheme.FiniteEtale (Spec (.of K))}
    (σ : Gal(Kbar/K))
    (ybar : ((specFieldGeometricPoint K Kbar).finiteFiber).obj Y) :
    ((specFieldGeometricPoint K Kbar).finiteFiber).obj Y :=
  Over.homMk (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ ybar.left)
    (w := galoisAlgClosure_smul_fac (K := K) (Kbar := Kbar) σ ybar)

/-- The raw precomposition action satisfies the identity law. -/
theorem galoisAlgClosure_one_smul {K Kbar : Type u}
    [Field K] [Field Kbar] [Algebra K Kbar] [IsAlgClosed Kbar]
    {Y : Scheme.FiniteEtale (Spec (.of K))}
    (ybar : ((specFieldGeometricPoint K Kbar).finiteFiber).obj Y) :
    galoisAlgClosure_smul (1 : Gal(Kbar/K)) ybar = ybar := sorry

/-- The raw precomposition action satisfies the multiplication law. -/
theorem galoisAlgClosure_mul_smul {K Kbar : Type u}
    [Field K] [Field Kbar] [Algebra K Kbar] [IsAlgClosed Kbar]
    {Y : Scheme.FiniteEtale (Spec (.of K))}
    (σ τ : Gal(Kbar/K))
    (ybar : ((specFieldGeometricPoint K Kbar).finiteFiber).obj Y) :
    galoisAlgClosure_smul (σ * τ) ybar =
      galoisAlgClosure_smul σ (galoisAlgClosure_smul τ ybar) := sorry

/-- The canonical action of algebraic-closure automorphisms on each finite geometric fiber. -/
instance galoisAlgClosureMulAction (K Kbar : Type u)
    [Field K] [Field Kbar] [Algebra K Kbar] [IsAlgClosed Kbar]
    (Y : Scheme.FiniteEtale (Spec (.of K))) :
    MulAction Gal(Kbar/K) (((specFieldGeometricPoint K Kbar).finiteFiber).obj Y) where
  smul := galoisAlgClosure_smul
  one_smul := galoisAlgClosure_one_smul (K := K) (Kbar := Kbar)
  mul_smul := galoisAlgClosure_mul_smul (K := K) (Kbar := Kbar)

/-- The underlying scheme morphism of precomposition by an automorphism. -/
theorem galoisAlgClosure_smul_apply {K Kbar : Type u}
    [Field K] [Field Kbar] [Algebra K Kbar] [IsAlgClosed Kbar]
    {Y : Scheme.FiniteEtale (Spec (.of K))}
    (σ : Gal(Kbar/K))
    (ybar : ((specFieldGeometricPoint K Kbar).finiteFiber).obj Y) :
    (galoisAlgClosure_smul σ ybar).left =
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ ybar.left := rfl

/-- Precomposition commutes with the finite-fiber map of every finite étale morphism. -/
theorem galoisAlgClosure_smul_map {K Kbar : Type u}
    [Field K] [Field Kbar] [Algebra K Kbar] [IsAlgClosed Kbar]
    {Y Z : Scheme.FiniteEtale (Spec (.of K))} (f : Y ⟶ Z)
    (σ : Gal(Kbar/K))
    (ybar : ((specFieldGeometricPoint K Kbar).finiteFiber).obj Y) :
    ((specFieldGeometricPoint K Kbar).finiteFiber).map f (galoisAlgClosure_smul σ ybar) =
      galoisAlgClosure_smul σ (((specFieldGeometricPoint K Kbar).finiteFiber).map f ybar) := sorry

/-- The algebraic-closure action is natural on the finite-fiber functor. -/
instance galoisAlgClosureNaturalSMul (K Kbar : Type u)
    [Field K] [Field Kbar] [Algebra K Kbar] [IsAlgClosed Kbar] :
    PreGaloisCategory.IsNaturalSMul (specFieldGeometricPoint K Kbar).finiteFiber Gal(Kbar/K) where
  naturality σ {X Y} f ybar :=
    galoisAlgClosure_smul_map (K := K) (Kbar := Kbar) f σ ybar

/-- The explicit homomorphism from algebraic-closure automorphisms to automorphisms of the
finite geometric-fiber functor. -/
noncomputable def galoisAlgClosureToFundamentalGroup (K Kbar : Type u)
    [Field K] [Field Kbar] [Algebra K Kbar] [IsAlgClosed Kbar] :
    Gal(Kbar/K) →* Aut ((specFieldGeometricPoint K Kbar).finiteFiber) :=
  PreGaloisCategory.toAut (specFieldGeometricPoint K Kbar).finiteFiber Gal(Kbar/K)

/-- The explicit algebraic-closure action agrees with the canonical separable-closure comparison
after restriction along the closure automorphism equivalence. -/
theorem galoisAlgClosureToFundamentalGroup_comp_restrict (K Kbar Ksep : Type u)
    [Field K] [Field Kbar] [Field Ksep]
    [Algebra K Kbar] [Algebra K Ksep] [Algebra Ksep Kbar]
    [IsScalarTower K Ksep Kbar] [IsAlgClosed Kbar] [IsAlgClosure K Kbar]
    [IsSepClosure K Ksep] :
    (galoisAlgClosureToFundamentalGroup K Kbar).comp
        (AlgEquiv.sepClosureEquivAlgClosure K Kbar Ksep).toMonoidHom =
      (galoisToFundamentalGroup K Kbar Ksep).toMonoidHom := sorry

end AlgebraicGeometry.Scheme.Etale

end
