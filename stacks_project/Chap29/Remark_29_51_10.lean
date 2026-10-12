/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.GenericallyFinite
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Remark 29.51.10 (1): target-local generic finiteness means that every fiber over a generic
point of the target is finite. -/
@[stacks 073A] #check
  (AlgebraicGeometry.Scheme.Hom.genericallyFiniteOnTarget_iff :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      f.GenericallyFiniteOnTarget ↔
        ∀ η : Y, η ∈ genericPoints Y →
          ({x : X | f.base x = η} : Set X).Finite)

/- Remark 29.51.10 (2): source-local generic finiteness means that the morphism is locally
quasi-finite on some dense open subscheme of the source. -/
@[stacks 073A] #check
  (AlgebraicGeometry.Scheme.Hom.genericallyFiniteOnSource_iff :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      f.GenericallyFiniteOnSource ↔
        ∃ U : X.Opens, Dense (U : Set X) ∧ LocallyQuasiFinite (U.ι ≫ f))

/- Remark 29.51.10 (3): a quasi-compact, locally finite type morphism that is generically finite
on the source is generically finite on the target when the target has finitely many irreducible
components on quasi-compact opens. -/
@[stacks 073A] #check
  (AlgebraicGeometry.Scheme.Hom.genericallyFiniteOnTarget_of_genericallyFiniteOnSource :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      [LocallyOfFiniteType f] → [QuasiCompact f] →
      [AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens Y] →
      f.GenericallyFiniteOnSource → f.GenericallyFiniteOnTarget)
