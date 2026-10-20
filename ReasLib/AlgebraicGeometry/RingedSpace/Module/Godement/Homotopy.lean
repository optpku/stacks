/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Godement.Flasque
public import ReasLib.AlgebraicTopology.CosimplicialObject.Homotopy.Equiv.Functor
public import ReasLib.AlgebraicTopology.CosimplicialObject.Homotopy.Equiv.QuasiIso
public import ReasLib.CategoryTheory.Adjunction.CosimplicialResolution.Contraction
public import ReasLib.CategoryTheory.Pi.Preadditive

/-!
# Homotopy properties of the Godement resolution

The Godement monad comes from the adjunction between module sheaves and point-indexed modules.
After applying the left adjoint, the monad resolution has the counit-induced last extra
codegeneracy, hence is contractible.  This file exposes that contraction first as structured
cosimplicial data, then as homotopy-equivalence and quasi-isomorphism properties of the associated
cochain-complex augmentations.
-/

@[expose] public section

open CategoryTheory
open AlgebraicTopology
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Godement

/-- The monad resolution after applying the point-family functor.  Its augmentation point is
`toDiscrete X`, and the adjunction counit contracts its cosimplicial part. -/
@[stacks 0FKS "Godement resolution after pullback to all points"]
noncomputable abbrev discreteAugmented (X : RingedSpace.{u}) :
    CosimplicialObject.Augmented (X.Modules ⥤ Discrete X) :=
  CategoryTheory.Adjunction.CosimplicialResolution.postcompose (adjunction X)

/-- The constant cosimplicial point-family object occurring as the source of the discrete
Godement coaugmentation. -/
noncomputable abbrev discreteConstant (X : RingedSpace.{u}) (F : X.Modules) :
    CosimplicialObject (Discrete X) :=
  (CosimplicialObject.const (Discrete X)).obj ((discreteAugmented X).left.obj F)

/-- The cosimplicial point-family object obtained by evaluating the postcomposed Godement
resolution at `F`. -/
noncomputable abbrev discreteCosimplicial (X : RingedSpace.{u}) (F : X.Modules) :
    CosimplicialObject (Discrete X) :=
  (discreteAugmented X).right.flip.obj F

/-- The explicit counit-induced homotopy equivalence contracting the Godement resolution after
pullback to every point. -/
@[stacks 0FKS "point-family contraction of the Godement resolution"]
noncomputable def discreteEquiv (X : RingedSpace.{u}) (F : X.Modules) :
    CosimplicialObject.HomotopyEquiv
      (discreteConstant X F) (discreteCosimplicial X F) :=
  (CategoryTheory.Adjunction.CosimplicialResolution.postcompose.homotopyEquiv
      (adjunction X)).app F

/-- The coaugmentation underlying the point-family contraction of the Godement resolution. -/
@[stacks 0FKS "point-family Godement coaugmentation"]
noncomputable abbrev discreteCoaugmentation (X : RingedSpace.{u}) (F : X.Modules) :
    discreteConstant X F ⟶ discreteCosimplicial X F :=
  (discreteEquiv X F).hom

/-- Evaluating the point-family contraction at `x` gives explicit cosimplicial homotopy-
equivalence data in modules over the stalk ring at `x`. -/
@[stacks 0FKS "pointwise contraction of the Godement resolution"]
noncomputable def pointEquiv (X : RingedSpace.{u}) (F : X.Modules) (x : X) :
    CosimplicialObject.HomotopyEquiv
      (discreteConstant X F ⋙ CategoryTheory.Pi.eval
        (fun y : X ↦ ModuleCat.{u} (RingCat.of (X.presheaf.stalk y))) x)
      (discreteCosimplicial X F ⋙ CategoryTheory.Pi.eval
        (fun y : X ↦ ModuleCat.{u} (RingCat.of (X.presheaf.stalk y))) x) :=
  (discreteEquiv X F).whiskerRight
    (CategoryTheory.Pi.eval
      (fun y : X ↦ ModuleCat.{u} (RingCat.of (X.presheaf.stalk y))) x)

/-- The Godement augmentation after applying the full point-family functor degreewise. -/
@[stacks 0FKS "point-family Godement complex augmentation"]
noncomputable abbrev discreteAugmentation (X : RingedSpace.{u}) (F : X.Modules) :=
  ((toDiscrete X).mapHomologicalComplex (ComplexShape.up ℕ)).map
    ((augmentation X).app F)

/-- The Godement augmentation after applying the pullback model of the stalk functor at `x`
degreewise. -/
@[stacks 0FKS "point-pullback Godement complex augmentation"]
noncomputable abbrev pointAugmentation
    (X : RingedSpace.{u}) (F : X.Modules) (x : X) :=
  ((RingedSpace.Module.pointPullbackFunctor x).mapHomologicalComplex
    (ComplexShape.up ℕ)).map ((augmentation X).app F)

/-- The Godement augmentation after applying the canonical module-stalk functor at `x`
degreewise. -/
@[stacks 0FKS "stalkwise Godement complex augmentation"]
noncomputable abbrev stalkAugmentation
    (X : RingedSpace.{u}) (F : X.Modules) (x : X) :=
  ((RingedSpace.stalkModuleFunctor x).mapHomologicalComplex
    (ComplexShape.up ℕ)).map ((augmentation X).app F)

/-- Pullback to the full family of points makes the Godement complex augmentation a chain
homotopy equivalence. -/
@[stacks 0FKS "point-family Godement augmentation is a homotopy equivalence"]
theorem discreteAugmentation_homotopyEquivalence
    (X : RingedSpace.{u}) (F : X.Modules) :
    HomologicalComplex.homotopyEquivalences (Discrete X) (ComplexShape.up ℕ)
      (discreteAugmentation X F) := sorry

/-- Pullback to a single point makes the Godement complex augmentation a chain homotopy
equivalence. -/
@[stacks 0FKS "point-pullback Godement augmentation is a homotopy equivalence"]
theorem pointAugmentation_homotopyEquivalence
    (X : RingedSpace.{u}) (F : X.Modules) (x : X) :
    HomologicalComplex.homotopyEquivalences
      (ModuleCat (X.presheaf.stalk x)) (ComplexShape.up ℕ)
      (pointAugmentation X F x) := sorry

/-- Lemma 20.30.1, stalkwise clause: the canonical stalk of the Godement complex augmentation is
a chain homotopy equivalence. -/
@[stacks 0FKS "stalkwise Godement augmentation is a homotopy equivalence"]
theorem stalkAugmentation_homotopyEquivalence
    (X : RingedSpace.{u}) (F : X.Modules) (x : X) :
    HomologicalComplex.homotopyEquivalences
      (ModuleCat (X.presheaf.stalk x)) (ComplexShape.up ℕ)
      (stalkAugmentation X F x) := sorry

/-- Lemma 20.30.1, resolution clause: the functorial Godement complex augmentation is a
quasi-isomorphism. -/
@[stacks 0FKS "Godement resolution quasi-isomorphism"]
theorem augmentation_quasiIso (X : RingedSpace.{u}) (F : X.Modules) :
    QuasiIso ((augmentation X).app F) := sorry

end AlgebraicGeometry.RingedSpace.Godement
