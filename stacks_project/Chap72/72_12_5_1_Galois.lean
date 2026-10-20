/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.Basic
public import stacks_project.Chap65.Lemma_65_7_1_Product
public import stacks_project.Chap66.Definition_66_4_1_Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldExtension.Galois

/-!
# Galois automorphisms of field-extension base changes of algebraic spaces

The fibre product `Spec K ×_{Spec k} X` of an algebraic space `X` over a field `k`
carries a canonical action of `Gal(K/k)ᵐᵒᵖ` by automorphisms over `Spec k`, induced
by `Spec(σ) × id`.
-/


@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
variable (X : AlgebraicSpace (Spec (CommRingCat.of k)))

#check (AlgebraicGeometry.AlgebraicSpace.FieldExtension.Galois.opAutHom k K X :
  (Gal(K/k))ᵐᵒᵖ →* Aut (AlgebraicGeometry.AlgebraicSpace.FieldExtension.baseChange k K X))

end

end
