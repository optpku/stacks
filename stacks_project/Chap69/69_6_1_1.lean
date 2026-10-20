/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Koszul.Augmentation
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- 69.6.1.1: if `f : U ⟶ X` is a surjective étale morphism of algebraic spaces, the
truncated Koszul complex `K^•(f)` of the trace `Tr_f : f_! ℤ̲ ⟶ ℤ̲`
has terms `K^i(f) = ⋀^{i+1}(f_! ℤ̲)`, and its canonical augmentation to
`ℤ̲[0]` is a quasi-isomorphism in `Ab(X_étale)`. -/
@[stacks 0723] #check (AlgebraicGeometry.AlgebraicSpace.instQuasiIsoTraceKoszulToConstant :
  ∀ {S : Scheme.{u}} {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f] [Surjective f],
    QuasiIso (AlgebraicGeometry.AlgebraicSpace.traceKoszulToConstant f))

#check (AlgebraicGeometry.AlgebraicSpace.traceKoszulToConstant :
  ∀ {S : Scheme.{u}} {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f] [Surjective f],
    koszulComplex f ⟶
      (ChainComplex.single₀
        (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})).obj
        (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology X)))
