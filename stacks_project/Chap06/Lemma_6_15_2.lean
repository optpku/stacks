/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.Algebraic.Instances
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 6.15.2 (1): pointed sets form a type of algebraic structures. -/
@[stacks 007N "pointed sets"]
#check pointedAlgebraicStructure

/- Lemma 6.15.2 (2): abelian groups form a type of algebraic structures. -/
@[stacks 007N "abelian groups"]
#check addCommGrpCatAlgebraicStructure

/- Lemma 6.15.2 (3): groups form a type of algebraic structures. -/
@[stacks 007N "groups"]
#check grpCatAlgebraicStructure

/- Lemma 6.15.2 (4): monoids form a type of algebraic structures. -/
@[stacks 007N "monoids"]
#check monCatAlgebraicStructure

/- Lemma 6.15.2 (5): commutative rings with `1` form a type of algebraic structures. -/
@[stacks 007N "rings"]
#check commRingCatAlgebraicStructure

variable (R : Type u) [CommRing R]

/- Lemma 6.15.2 (6): modules over a fixed commutative ring form a type of algebraic
structures. -/
@[stacks 007N "modules over a fixed ring"]
#check (moduleCatAlgebraicStructureOfCommRing R :
  IsAlgebraicStructure (ModuleCat.{v} R) (CategoryTheory.forget (ModuleCat.{v} R)))

variable (k : Type u) [Field k]

/- Lemma 6.15.2 (7): Lie algebras over a fixed field form a type of algebraic structures. -/
@[stacks 007N "Lie algebras over a fixed field"]
#check (lieAlgebraCatAlgebraicStructureOfField k :
  IsAlgebraicStructure (LieAlgebraCat.{v} k) (CategoryTheory.forget (LieAlgebraCat.{v} k)))
