module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.AffineVanishingH1
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.CohomologyBaseChange

/-!
# Lemma 69.16.3

Affine morphisms preserve first-cohomology vanishing in Situation 69.16.1.
Spectrum base change has affine projection and the prescribed ring of global sections.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 69.16.3 (1): First cohomology of every quasi-coherent module vanishes
on the domain of an affine morphism in Situation 69.16.1. -/
@[stacks 07V0] #check (AlgebraicGeometry.AlgebraicSpace.cohomology_isZero_of_affine :
  ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasVanishingH1 X]
    [HasSheafify (smallEtaleTopology X') AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X') AddCommGrpCat.{u})]
    (f : X' ⟶ X) [Affine f] (F : Modules X'),
    quasiCoherentModuleProperty X' F → IsZero (cohomology X' F 1))

/- Lemma 69.16.3 (2): The projection from spectrum base change is affine. -/
@[stacks 07V0] #check (AlgebraicGeometry.AlgebraicSpace.affine_baseChangeSpecHom :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) {A' : CommRingCat.{u}}
    (φ : globalSectionsRing X ⟶ A'), Affine (baseChangeSpecHom X φ))

/- Lemma 69.16.3 (2): The canonical map from the base-change ring to global
sections is invertible in Situation 69.16.1. -/
@[stacks 07V0] #check (AlgebraicGeometry.AlgebraicSpace.globalSectionsRing_baseChangeSpec :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasVanishingH1 X] {A' : CommRingCat.{u}} (φ : globalSectionsRing X ⟶ A'),
    IsIso (baseChangeSpecGlobalSectionsMap X φ))
