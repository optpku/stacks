/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldExtension.Galois
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FieldExtension

/-!
# Field-extension base change of algebraic spaces and modules

The fibre product `Spec K ×_{Spec k} X` of an algebraic space `X` over a field `k`
is the chosen representative of `X_K`, with projections to `X` and to `Spec K`.
Pullback of modules along the source projection is the chosen `F_K`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FieldExtension

/-- The projection from the field-extension base change back to `X`. -/
abbrev toSource (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    baseChange k K X ⟶ X :=
  baseChangeSnd k K X

end AlgebraicGeometry.AlgebraicSpace.FieldExtension

#check (AlgebraicGeometry.AlgebraicSpace.FieldExtension.specOver :
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K],
    AlgebraicSpace (Spec (CommRingCat.of k)))

#check (AlgebraicGeometry.AlgebraicSpace.FieldExtension.baseChange :
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K],
    AlgebraicSpace (Spec (CommRingCat.of k)) → AlgebraicSpace (Spec (CommRingCat.of k)))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.FieldExtension.baseChange :
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))},
    X.Modules → (GenericFiber.baseChange k K X).Modules)
