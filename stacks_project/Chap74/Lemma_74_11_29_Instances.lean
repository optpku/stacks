/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiniteLocallyFree.Fpqc
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction

/-!
# Finite locally free morphisms are fpqc local on the target

Finite locally free morphisms of algebraic spaces over a scheme `S` satisfy
`IsLocalAtTarget` for the fpqc precoverage.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (Hom.pushforwardStructureModule :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Y.Modules)

#check (Modules.pushforwardStructureModule :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Y.Modules)

#check (FiniteLocallyFree :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)

#check (finiteLocallyFree_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    FiniteLocallyFree f ↔
      Affine f ∧ SheafOfModules.IsFiniteLocallyFree (Hom.pushforwardStructureModule f))

#check (FiniteLocallyFree.id :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}, FiniteLocallyFree (𝟙 X))

#check (FiniteLocallyFree.spec :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [FiniteLocallyFree f],
    Affine f ∧ SheafOfModules.IsFiniteLocallyFree (Hom.pushforwardStructureModule f))

#check (FiniteLocallyFree.isLocalAtTargetFpqc :
  ∀ {S : Scheme.{u}}, MorphismProperty.IsLocalAtTarget
    (@FiniteLocallyFree S : MorphismProperty (AlgebraicSpace S)) (fpqcPrecoverage S))

#check (FiniteLocallyFree.iff_forall_pullbackSnd_fpqc :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) {R : Presieve Y},
    R ∈ (fpqcPrecoverage S).coverings Y →
      (FiniteLocallyFree f ↔
        ∀ {U : AlgebraicSpace S} (g : U ⟶ Y) [HasPullback f g],
          R g → FiniteLocallyFree (pullback.snd f g)))

end AlgebraicGeometry.AlgebraicSpace
