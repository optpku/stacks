/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Extension

@[expose] public section

open AlgebraicGeometry CategoryTheory RingedSpace.Hom.IsFlat

noncomputable section

universe u

/- Lemma 36.13.3: a pseudo-coherent derived module on a quasi-compact open subscheme
of an affine scheme is the derived restriction of a bounded-above complex of finite-free
module sheaves. -/
@[stacks 08EE] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.PseudoCoherent.exists_finiteFree_extension :
    ∀ {X U : Scheme.{u}} [IsAffine X]
      (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
      (E : RingedSpace.ModuleDerived U.toRingedSpace)
      (_ : RingedSpace.ModuleDerived.IsPseudoCoherent E),
      ∃ (P : CochainComplex (RingedSpace.Modules X.toRingedSpace) ℤ)
        (e : (exactPullback j.toShHom).mapDerivedCategory.obj
          (DerivedCategory.Q.obj P) ≅ E),
        CochainComplex.minus (RingedSpace.Modules X.toRingedSpace) P ∧
          ∀ i, SheafOfModules.IsFiniteFree (P.X i))
