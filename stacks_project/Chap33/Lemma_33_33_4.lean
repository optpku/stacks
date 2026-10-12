/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.EulerCharacteristic.BaseChange

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 33.33.4: for a field extension `k'/k`, a proper `k`-scheme `X`, and a coherent sheaf
`ℱ` on `X`, the Euler characteristic of `ℱ` equals that of its pullback to `X_{k'}`. -/
@[stacks 08AB] #check
  (AlgebraicGeometry.Scheme.Hom.eulerCharacteristic_baseChange_of_fieldExtension :
    ∀ {k k' : Type u} [Field k] [Field k'] [Algebra k k']
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (ℱ : X.Modules) [ℱ.IsCoherent],
      Scheme.Hom.eulerCharacteristic f ℱ =
        Scheme.Hom.eulerCharacteristic
          (FieldExtension.toBase k k' f)
          (Scheme.Modules.FieldExtension.baseChange k k' f ℱ))
