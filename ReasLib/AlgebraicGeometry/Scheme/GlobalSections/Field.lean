/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The global-sections algebra of an integral scheme universally closed over a field carries
its canonical field structure. -/
@[implicit_reducible]
noncomputable def globalSectionsField
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsIntegral X] [UniversallyClosed f] :
    Field (globalSectionsAlg f) :=
  (AlgebraicGeometry.isField_of_universallyClosed k f).toField

end AlgebraicGeometry.Scheme.Hom
