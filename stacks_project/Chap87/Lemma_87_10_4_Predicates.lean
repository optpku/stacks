module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.SequentialSpf

/-!
# Sequential formal-spectrum presentation predicates

The four ring-theoretic presentations are provided by their canonical mathematical owner.
-/

open CategoryTheory CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite

universe u

#check (AlgebraicGeometry.IsAffineFormalAlgebraicSpace.isColimitOfCountablyGeneratedSpf :
  ∀ {S : Scheme.{u}}
    [HasWeakSheafify (full.bigTopology S) (Type (u + 1))],
    ((full.bigSite S)ᵒᵖ ⥤ Type (u + 1)) → Prop)

#check (AlgebraicGeometry.IsAffineFormalAlgebraicSpace.isColimitOfWeakIdealSequence :
  ∀ {S : Scheme.{u}}
    [HasWeakSheafify (full.bigTopology S) (Type (u + 1))],
    ((full.bigSite S)ᵒᵖ ⥤ Type (u + 1)) → Prop)

#check (AlgebraicGeometry.IsAffineFormalAlgebraicSpace.isColimitOfCompleteLocallyNilpotentSequence :
  ∀ {S : Scheme.{u}}
    [HasWeakSheafify (full.bigTopology S) (Type (u + 1))],
    ((full.bigSite S)ᵒᵖ ⥤ Type (u + 1)) → Prop)

#check (AlgebraicGeometry.IsAffineFormalAlgebraicSpace.isColimitOfQuotientInverseLimit :
  ∀ {S : Scheme.{u}}
    [HasWeakSheafify (full.bigTopology S) (Type (u + 1))],
    ((full.bigSite S)ᵒᵖ ⥤ Type (u + 1)) → Prop)

