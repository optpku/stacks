/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Semistable

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Residue-field fibres and the semistability predicates for schemes. -/
#check (AlgebraicGeometry.SchemeOverField.fibreOverField :
  ∀ {X S : Scheme.{u}}, (X ⟶ S) → ∀ s : S, SchemeOverField (S.residueField s))

#check (AlgebraicGeometry.SchemeOverField.IsSemistableFibre :
  ∀ {k : Type u} [Field k], SchemeOverField k → Prop)

#check (AlgebraicGeometry.Semistable :
  ∀ {X S : Scheme.{u}}, (X ⟶ S) → Prop)
