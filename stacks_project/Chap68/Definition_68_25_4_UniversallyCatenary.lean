module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyCatenary
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

#check (AlgebraicGeometry.AlgebraicSpace.UniversallyCatenary :
  ∀ {S : Scheme.{u}}, AlgebraicSpace S → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.universallyCatenary_iff :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    UniversallyCatenary X ↔
      IsLocallyNoetherian X ∧ IsDecent X ∧
        ∀ {Y : AlgebraicSpace S} (f : Y ⟶ X),
          LocallyOfFiniteType f → IsDecent Y → IsCatenary Y)

#check (AlgebraicGeometry.AlgebraicSpace.instIsCatenary :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [UniversallyCatenary X],
    IsCatenary X)

#check (AlgebraicGeometry.AlgebraicSpace.instUniversallyCatenary_ofOver :
  ∀ {S : Scheme.{u}} (T : Over S) [AlgebraicGeometry.UniversallyCatenary T.left],
    UniversallyCatenary (ofOver T))

#check (AlgebraicGeometry.AlgebraicSpace.universallyCatenary_iff_quasiSeparated :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsLocallyNoetherian X] [IsDecent X],
    UniversallyCatenary X ↔
      ∀ {Y : AlgebraicSpace S} (f : Y ⟶ X),
        LocallyOfFiniteType f → IsQuasiSeparated Y → IsCatenary Y)

end AlgebraicGeometry.AlgebraicSpace
