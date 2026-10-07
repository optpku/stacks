module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.GenericPoints.FiniteNeighborhood

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 33.17.2 (1): finite residue-field extensions at every generic point. -/
@[stacks 0AB7] #check
  (AlgebraicGeometry.Scheme.Hom.exists_isFinite_morphismRestrict_of_finiteGenericResidues :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (y : Y),
      IsNoetherianRing (Y.presheaf.stalk y) →
      ringKrullDim (Y.presheaf.stalk y) ≤ 1 →
      AlgebraicGeometry.Scheme.Hom.GenericPoints.finiteResidues f →
      ∃ V : Y.Opens, y ∈ V ∧ IsFinite (f ∣_ V))

/- Lemma 33.17.2 (2): algebraic residue-field extensions at every generic point. -/
@[stacks 0AB7] #check
  (AlgebraicGeometry.Scheme.Hom.exists_isFinite_morphismRestrict_of_algebraicGenericResidues :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (y : Y),
      IsNoetherianRing (Y.presheaf.stalk y) →
      ringKrullDim (Y.presheaf.stalk y) ≤ 1 →
      AlgebraicGeometry.Scheme.Hom.GenericPoints.algebraicResidues f →
      ∃ V : Y.Opens, y ∈ V ∧ IsFinite (f ∣_ V))

/- Lemma 33.17.2 (3): finite residue-field extensions at the generic points specializing over
`y`. -/
@[stacks 0AB7] #check
  (AlgebraicGeometry.Scheme.Hom.exists_isFinite_morphismRestrict_of_finiteGenericResiduesOver :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (y : Y),
      IsNoetherianRing (Y.presheaf.stalk y) →
      ringKrullDim (Y.presheaf.stalk y) ≤ 1 →
      AlgebraicGeometry.Scheme.Hom.GenericPoints.finiteResiduesOver f y →
      ∃ V : Y.Opens, y ∈ V ∧ IsFinite (f ∣_ V))

/- Lemma 33.17.2 (4): algebraic residue-field extensions at the generic points specializing over
`y`. -/
@[stacks 0AB7] #check
  (AlgebraicGeometry.Scheme.Hom.exists_isFinite_morphismRestrict_of_algebraicGenericResiduesOver :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (y : Y),
      IsNoetherianRing (Y.presheaf.stalk y) →
      ringKrullDim (Y.presheaf.stalk y) ≤ 1 →
      AlgebraicGeometry.Scheme.Hom.GenericPoints.algebraicResiduesOver f y →
      ∃ V : Y.Opens, y ∈ V ∧ IsFinite (f ∣_ V))

/- Lemma 33.17.2 (5): quasi-finiteness at every generic point. -/
@[stacks 0AB7] #check
  (AlgebraicGeometry.Scheme.Hom.exists_isFinite_morphismRestrict_of_quasiFiniteAtGenericPoints :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (y : Y),
      IsNoetherianRing (Y.presheaf.stalk y) →
      ringKrullDim (Y.presheaf.stalk y) ≤ 1 →
      AlgebraicGeometry.Scheme.Hom.GenericPoints.quasiFinite f →
      ∃ V : Y.Opens, y ∈ V ∧ IsFinite (f ∣_ V))

/- Lemma 33.17.2 (6): a dense quasi-finite locus over a locally Noetherian target. -/
@[stacks 0AB7] #check
  (AlgebraicGeometry.Scheme.Hom.exists_isFinite_morphismRestrict_of_denseQuasiFiniteLocus :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y] (y : Y),
      IsNoetherianRing (Y.presheaf.stalk y) →
      ringKrullDim (Y.presheaf.stalk y) ≤ 1 →
      AlgebraicGeometry.Scheme.Hom.QuasiFinite.hasDenseLocus f →
      ∃ V : Y.Opens, y ∈ V ∧ IsFinite (f ∣_ V))
