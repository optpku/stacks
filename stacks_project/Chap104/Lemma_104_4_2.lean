/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.DerivedSections.Abelian
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.DerivedSections.Module
import StacksCheckRecall

/-!
# Lemma 104.4.2

Derived global sections and sections over every object agree after restriction
from the étale site to the lisse-étale site and from the fppf site to the
flat-fppf site, for abelian sheaves and for modules on an algebraic stack.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory

universe u z

variable {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
variable [UnivLE.{u + 1, z}]

/- Lemma 104.4.2: global abelian comparison. -/
@[stacks 0H10] #check
  (AlgebraicGeometry.AlgebraicStack.lisseEtaleAbelianDerivedGlobalSectionsComparison.instIsIso.{u, z} X :
    IsIso
      (AlgebraicGeometry.AlgebraicStack.lisseEtaleAbelianDerivedGlobalSectionsComparison.{u, z} X))

/- Lemma 104.4.2: objectwise abelian comparison. -/
@[stacks 0H10] #check
  (AlgebraicGeometry.AlgebraicStack.lisseEtaleAbelianDerivedSectionsComparison.instIsIso.{u, z} X :
    ∀ x : AlgebraicGeometry.AlgebraicStack.lisseEtaleSite X, IsIso
      (AlgebraicGeometry.AlgebraicStack.lisseEtaleAbelianDerivedSectionsComparison.{u, z} X x))

/- Lemma 104.4.2: global abelian comparison. -/
@[stacks 0H10] #check
  (AlgebraicGeometry.AlgebraicStack.flatFppfAbelianDerivedGlobalSectionsComparison.instIsIso.{u, z} X :
    IsIso
      (AlgebraicGeometry.AlgebraicStack.flatFppfAbelianDerivedGlobalSectionsComparison.{u, z} X))

/- Lemma 104.4.2: objectwise abelian comparison. -/
@[stacks 0H10] #check
  (AlgebraicGeometry.AlgebraicStack.flatFppfAbelianDerivedSectionsComparison.instIsIso.{u, z} X :
    ∀ x : AlgebraicGeometry.AlgebraicStack.flatFppfSite X, IsIso
      (AlgebraicGeometry.AlgebraicStack.flatFppfAbelianDerivedSectionsComparison.{u, z} X x))

/- Lemma 104.4.2: global module comparison. -/
@[stacks 0H10] #check
  (AlgebraicGeometry.AlgebraicStack.lisseEtaleModuleDerivedGlobalSectionsComparison.instIsIso.{u, z} X :
    IsIso
      (AlgebraicGeometry.AlgebraicStack.lisseEtaleModuleDerivedGlobalSectionsComparison.{u, z} X))

/- Lemma 104.4.2: objectwise module comparison. -/
@[stacks 0H10] #check
  (AlgebraicGeometry.AlgebraicStack.lisseEtaleModuleDerivedSectionsComparison.instIsIso.{u, z} X :
    ∀ x : AlgebraicGeometry.AlgebraicStack.lisseEtaleSite X, IsIso
      (AlgebraicGeometry.AlgebraicStack.lisseEtaleModuleDerivedSectionsComparison.{u, z} X x))

/- Lemma 104.4.2: global module comparison. -/
@[stacks 0H10] #check
  (AlgebraicGeometry.AlgebraicStack.flatFppfModuleDerivedGlobalSectionsComparison.instIsIso.{u, z} X :
    IsIso
      (AlgebraicGeometry.AlgebraicStack.flatFppfModuleDerivedGlobalSectionsComparison.{u, z} X))

/- Lemma 104.4.2: objectwise module comparison. -/
@[stacks 0H10] #check
  (AlgebraicGeometry.AlgebraicStack.flatFppfModuleDerivedSectionsComparison.instIsIso.{u, z} X :
    ∀ x : AlgebraicGeometry.AlgebraicStack.flatFppfSite X, IsIso
      (AlgebraicGeometry.AlgebraicStack.flatFppfModuleDerivedSectionsComparison.{u, z} X x))

