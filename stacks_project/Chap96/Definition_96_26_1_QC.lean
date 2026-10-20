/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Derived.QuasiCoherent

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open AlgebraicGeometry.GroupoidsOver CategoryTheory.ModulesOnCategory

universe u

/- The canonical comparison-map quasi-coherence property. -/
#check (AlgebraicGeometry.GroupoidsOver.qcProperty :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    ObjectProperty (RingedSite.Hom.ModuleDerived.{u + 1}
      (RingedSite.ofCommRingSheaf ⊥ (affineStructureSheaf X))))
#check (AlgebraicGeometry.GroupoidsOver.qcProperty_eq :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    qcProperty X = Chaotic.isQuasiCoherent.{u + 1, u, u} (affineStructureSheaf X))

/- The quasi-coherent derived category on the chaotic affine site. -/
#check (AlgebraicGeometry.GroupoidsOver.QC :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S), Type (u + 2))
#check (AlgebraicGeometry.GroupoidsOver.QC_eq :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    QC X = Chaotic.QC.{u + 1, u, u} (affineStructureSheaf X))
#check (AlgebraicGeometry.GroupoidsOver.mem_QC_iff :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    (K : RingedSite.Hom.ModuleDerived.{u + 1}
      (RingedSite.ofCommRingSheaf ⊥ (affineStructureSheaf X))),
    qcProperty X K ↔ ∀ ⦃U V : affineSite X⦄ (f : U ⟶ V),
      IsIso ((chaoticComparison.{u + 1, u, u} (affineStructureSheaf X) f).app K))

/- The canonical inclusion and its action on objects. -/
#check (AlgebraicGeometry.GroupoidsOver.QC.inclusion :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    QC X ⥤ RingedSite.Hom.ModuleDerived.{u + 1}
      (RingedSite.ofCommRingSheaf ⊥ (affineStructureSheaf X)))
#check (AlgebraicGeometry.GroupoidsOver.QC.inclusion_obj :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) (K : QC X),
    (QC.inclusion X).obj K = K.obj)
