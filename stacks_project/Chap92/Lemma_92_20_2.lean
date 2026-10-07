module

public import stacks_project.Chap92.Definition_92_20_1_Morphism
public import stacks_project.Chap92.Lemma_92_18_6_HomologyZero
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials
import Mathlib.Tactic.CrossRefAttribute

/-!
# Degree-zero homology of the cotangent complex of a morphism of ringed spaces

Lemma 92.20.2 identifies `H^0(L[f])` with the sheaf of relative differentials `Ω[f]`
for a morphism of ringed spaces.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

open RingedSpace.Hom

variable {X S : RingedSpace.{u}}

/-- The canonical comparison morphism `H^0(L[f]) ⟶ Ω[f]` of `O_X`-modules. -/
noncomputable abbrev homologyZeroMap (f : X ⟶ S) :
    (cotangentComplex f).homology 0 ⟶ Hom.differentials f :=
  CotangentComplex.homologyZeroMap (inverseImageStructureSheafHomComm f)

/-- Lemma 92.20.2. Let `f : (X, O_X) ⟶ (S, O_S)` be a morphism of ringed spaces.
Then `H^0(L[f]) = Ω[f]`. -/
@[stacks 08UV]
noncomputable abbrev homologyZeroIso (f : X ⟶ S) :
    (cotangentComplex f).homology 0 ≅ Hom.differentials f :=
  CotangentComplex.homologyZeroIso (inverseImageStructureSheafHomComm f)

/-- The canonical comparison morphism `homologyZeroMap` is an isomorphism. -/
instance homologyZeroMap_isIso (f : X ⟶ S) : IsIso (homologyZeroMap f) :=
  sorry

/-- The forward morphism of `homologyZeroIso` is `homologyZeroMap`. -/
theorem homologyZeroIso_hom (f : X ⟶ S) :
    (homologyZeroIso f).hom = homologyZeroMap f :=
  sorry

/-- The inverse morphism of `homologyZeroIso` is the inverse of `homologyZeroMap`. -/
theorem homologyZeroIso_inv (f : X ⟶ S) :
    (homologyZeroIso f).inv = inv (homologyZeroMap f) :=
  sorry

end AlgebraicGeometry.RingedSpace
