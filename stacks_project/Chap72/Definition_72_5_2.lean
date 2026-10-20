/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap67.Definition_67_18_1_Dominant
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap72.Definition_72_5_2_ResidueField

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Degree
import StacksCheckRecall

/-!
# Degree of a morphism of integral algebraic spaces

The source definition applies when the generic residue-field extension is
finite. The natural-number API totalizes it by zero for infinite extensions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/- Definition 72.5.2: Let `S` be a scheme. Let `X` and `Y` be integral algebraic
spaces over `S`. Let `f : X ⟶ Y` be locally of finite type and dominant. Assume
any of the equivalent conditions (1)–(5) of Lemma 72.5.1. Let `x ∈ Points X`
and `y ∈ Points Y` be the generic points. Then the positive integer
`degree f = [κ(x) : κ(y)]` is called the degree of `X` over `Y`, also written
`deg(X/Y)`. -/
@[stacks 0AD6] #check (AlgebraicGeometry.AlgebraicSpace.Hom.degree :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f]
    [Dominant f],
    ℕ)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.degree_eq_finrank :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f]
    [Dominant f] {x : Points X} (hx : x ∈ genericPoints X),
    degree f =
      -- Local instance justification (instance diamond): competing morphisms induce competing algebras on the same residue fields
      letI := (residueFieldMap f x).hom.toAlgebra
      Module.finrank (Y.residueField (Points.map f x)) (X.residueField x))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.degree_pos :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f]
    [Dominant f] (hf : FiniteResidueFieldExtension f),
    0 < degree f)

end AlgebraicGeometry.AlgebraicSpace.Hom
