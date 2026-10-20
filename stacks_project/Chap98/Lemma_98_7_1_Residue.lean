module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.ResidueExtension

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (k l : Type u) [Field k] [Field l] [Algebra k l]
variable (kToS : Spec (CommRingCat.of k) ⟶ S)

/- Lemma 98.7.1. The spectrum map induced by the residue-field extension. -/
#check (AlgebraicGeometry.GroupoidsOver.Predeformation.residueHom k l :
  Spec (CommRingCat.of l) ⟶ Spec (CommRingCat.of k))

/- Lemma 98.7.1. The extended residue field has the composite structure map to the base. -/
#check (AlgebraicGeometry.GroupoidsOver.Predeformation.lToS k l kToS :
  Spec (CommRingCat.of l) ⟶ S)
