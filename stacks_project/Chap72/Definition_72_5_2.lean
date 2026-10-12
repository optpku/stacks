/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_18_1_Dominant
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap72.Definition_72_5_2_ResidueField

/-!
# Degree of a morphism of integral algebraic spaces

The degree of a locally finite type dominant morphism of integral algebraic
spaces is the residue-field degree at the generic point, in the sense of
Stacks Definition 72.5.2.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- Definition 72.5.2: Let `S` be a scheme. Let `X` and `Y` be integral algebraic
spaces over `S`. Let `f : X ⟶ Y` be locally of finite type and dominant. Assume
any of the equivalent conditions (1)–(5) of Lemma 72.5.1. Let `x ∈ Points X`
and `y ∈ Points Y` be the generic points. Then the positive integer
`degree f = [κ(x) : κ(y)]` is called the degree of `X` over `Y`, also written
`deg(X/Y)`. -/
@[stacks 0AD6]
noncomputable def degree {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f]
    [Dominant f] : ℕ :=
  residueDegree f (exists_mem_genericPoints X).choose

/-- The residue-field extension at a generic point of an integral dominant
morphism of algebraic spaces is finite. -/
def FiniteResidueFieldExtension {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [Dominant f] : Prop :=
  ∀ ⦃x : Points X⦄, x ∈ genericPoints X → FiniteResidueFieldExtensionAt f x

/-- Finiteness of the generic residue-field extension is finite-dimensionality
of the algebra induced by `residueFieldHom` at any generic point. -/
theorem FiniteResidueFieldExtension_iff {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    [Dominant f] {x : Points X} (hx : x ∈ genericPoints X) :
    FiniteResidueFieldExtension f ↔
      -- Local instance justification (instance diamond): competing morphisms induce competing algebras on the same residue fields
      letI := (residueFieldHom f x).hom.toAlgebra
      FiniteDimensional (Y.residueField (Points.map f x))
        (X.residueField x) :=
  sorry

/-- The degree of `f` equals the residue degree at any generic point of `X`. -/
theorem degree_eq_residueDegree {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f]
    [Dominant f] {x : Points X} (hx : x ∈ genericPoints X) :
    degree f = residueDegree f x :=
  sorry

/-- The degree of `f` is the finrank `[κ(x) : κ(y)]` at a generic point `x`. -/
theorem degree_eq_finrank {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f]
    [Dominant f] {x : Points X} (hx : x ∈ genericPoints X) :
    degree f =
      -- Local instance justification (instance diamond): competing morphisms induce competing algebras on the same residue fields
      letI := (residueFieldHom f x).hom.toAlgebra
      Module.finrank (Y.residueField (Points.map f x)) (X.residueField x) :=
  sorry

/-- Under any of Lemma 72.5.1 (1)–(5), equivalently
`FiniteResidueFieldExtension`, the degree is a positive integer. -/
theorem degree_pos {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f]
    [Dominant f] (hf : FiniteResidueFieldExtension f) : 0 < degree f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
