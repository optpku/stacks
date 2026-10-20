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
