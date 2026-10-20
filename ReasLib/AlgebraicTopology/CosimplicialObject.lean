/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.CosimplicialObject.Abelian
public import ReasLib.AlgebraicTopology.CosimplicialObject.Monoidal
public import ReasLib.AlgebraicTopology.CosimplicialObject.Tensor.AlexanderWhitney
public import ReasLib.AlgebraicTopology.CosimplicialObject.Augmented.Composition
public import ReasLib.AlgebraicTopology.CosimplicialObject.Augmented.ExtraCodegeneracy
public import ReasLib.AlgebraicTopology.CosimplicialObject.Augmented.ExtraCodegeneracy.Homotopy
public import ReasLib.AlgebraicTopology.CosimplicialObject.Augmented.LastExtraCodegeneracy
public import ReasLib.AlgebraicTopology.CosimplicialObject.Augmented.LastExtraCodegeneracy.Homotopy
public import ReasLib.AlgebraicTopology.CosimplicialObject.Pullback
public import ReasLib.AlgebraicTopology.CosimplicialObject.Cotensor.Bifunctor
public import ReasLib.AlgebraicTopology.CosimplicialObject.Homotopy.Relation

/-!
# Base cosimplicial-object support

This aggregate exposes reusable augmented contractions, degreewise pullbacks, simplicial-set
cotensors, and canonical homotopy infrastructure for cosimplicial objects. Product-free and
opposite-simplicial homotopy presentations remain in their targeted descendant modules.
-/
