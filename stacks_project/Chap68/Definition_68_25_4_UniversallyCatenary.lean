/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap68.Definition_68_25_1_Catenary
public import stacks_project.Chap68.Lemma_68_12_8_Decent

/-!
# Universally catenary algebraic spaces

A decent locally Noetherian algebraic space is universally catenary when every
decent algebraic space locally of finite type over it is catenary.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A decent locally Noetherian algebraic space is universally catenary if every
locally of finite type morphism from a decent algebraic space has catenary
source. -/
class UniversallyCatenary {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop
    extends IsLocallyNoetherian X, IsDecent X where
  /-- Every locally of finite type morphism from a decent algebraic space has
  catenary source. -/
  isCatenary_of_locallyOfFiniteType {Y : AlgebraicSpace S} (f : Y ⟶ X)
    [LocallyOfFiniteType f] [IsDecent Y] : IsCatenary Y

/-- A decent locally Noetherian algebraic space is universally catenary exactly
when every locally of finite type morphism from a decent algebraic space has
catenary source. -/
theorem universallyCatenary_iff {S : Scheme.{u}} (X : AlgebraicSpace S) :
    UniversallyCatenary X ↔
      IsLocallyNoetherian X ∧ IsDecent X ∧
        ∀ {Y : AlgebraicSpace S} (f : Y ⟶ X),
          LocallyOfFiniteType f → IsDecent Y → IsCatenary Y :=
  sorry

/-- A universally catenary algebraic space is itself catenary. -/
instance instIsCatenary {S : Scheme.{u}} (X : AlgebraicSpace S)
    [UniversallyCatenary X] : IsCatenary X :=
  UniversallyCatenary.isCatenary_of_locallyOfFiniteType (𝟙 X)

/-- A universally catenary scheme over `S`, viewed as an algebraic space, is
universally catenary. -/
instance instUniversallyCatenary_ofOver {S : Scheme.{u}} (T : Over S)
    [AlgebraicGeometry.UniversallyCatenary T.left] :
    UniversallyCatenary (ofOver T) where
  isCatenary_of_locallyOfFiniteType := sorry

/-- Under the standing locally Noetherian and decent hypotheses, universal
catenarity may equivalently be tested on quasi-separated sources. -/
theorem universallyCatenary_iff_quasiSeparated {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsLocallyNoetherian X] [IsDecent X] :
    UniversallyCatenary X ↔
      ∀ {Y : AlgebraicSpace S} (f : Y ⟶ X),
        LocallyOfFiniteType f → IsQuasiSeparated Y → IsCatenary Y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
