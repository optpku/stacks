module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_27_7_LocallyQuasiFinite
public import stacks_project.Chap67.Lemma_67_38_8_Unramified
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty

/-!
# Separation axioms for morphisms of algebraic stacks

A morphism of algebraic stacks is DM, quasi-DM, separated, or quasi-separated
according as its relative 2-diagonal is unramified, locally quasi-finite,
proper, or both quasi-compact and quasi-separated, tested on scheme-slice
representing morphisms of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism of algebraic stacks is DM if its relative 2-diagonal is
unramified. Equivalently, the fibres of such a morphism are Deligne–Mumford
stacks. -/
@[mk_iff]
class DM {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- The relative 2-diagonal is unramified. -/
  unramified_diagonal :
    Groupoids.Hom.has (@AlgebraicSpace.Unramified S)
      (Hom.diagonal.{u + 1, u, u + 1} f)

namespace DM

/-- The identity morphism of an algebraic stack is DM. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    DM (𝟙 X) :=
  sorry

/-- The relative 2-diagonal of a DM morphism of algebraic stacks is
unramified. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [DM f] :
    Groupoids.Hom.has (@AlgebraicSpace.Unramified S)
      (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

end DM

/-- A morphism of algebraic stacks is quasi-DM if its relative 2-diagonal is
locally quasi-finite. Equivalently, the fibres of such a morphism are
quasi-DM. -/
@[mk_iff]
class QuasiDM {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- The relative 2-diagonal is locally quasi-finite. -/
  locallyQuasiFinite_diagonal :
    Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S)
      (Hom.diagonal.{u + 1, u, u + 1} f)

namespace QuasiDM

/-- The identity morphism of an algebraic stack is quasi-DM. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    QuasiDM (𝟙 X) :=
  sorry

/-- The relative 2-diagonal of a quasi-DM morphism of algebraic stacks is
locally quasi-finite. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [QuasiDM f] :
    Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S)
      (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

end QuasiDM

/-- A morphism of algebraic stacks is separated if its relative 2-diagonal is
proper, not merely a closed immersion. -/
@[mk_iff]
class Separated {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- The relative 2-diagonal is a proper morphism of algebraic spaces. -/
  proper_diagonal :
    Groupoids.Hom.has (@AlgebraicSpace.Proper S)
      (Hom.diagonal.{u + 1, u, u + 1} f)

namespace Separated

/-- The identity morphism of an algebraic stack is separated. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    Separated (𝟙 X) :=
  sorry

/-- The relative 2-diagonal of a separated morphism of algebraic stacks is
proper. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Separated f] :
    Groupoids.Hom.has (@AlgebraicSpace.Proper S)
      (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

end Separated

/-- A morphism of algebraic stacks is quasi-separated if its relative
2-diagonal is both quasi-compact and quasi-separated. -/
@[mk_iff]
class QuasiSeparated {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- The relative 2-diagonal is quasi-compact. -/
  quasiCompact_diagonal :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S)
      (Hom.diagonal.{u + 1, u, u + 1} f)
  /-- The relative 2-diagonal is quasi-separated. -/
  quasiSeparated_diagonal :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
      (Hom.diagonal.{u + 1, u, u + 1} f)

namespace QuasiSeparated

/-- The identity morphism of an algebraic stack is quasi-separated. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    QuasiSeparated (𝟙 X) :=
  sorry

/-- A morphism of algebraic stacks is quasi-separated if and only if its
relative 2-diagonal is quasi-compact and quasi-separated. -/
theorem iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    QuasiSeparated f ↔
      Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S)
          (Hom.diagonal.{u + 1, u, u + 1} f) ∧
        Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
          (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

/-- The relative 2-diagonal of a quasi-separated morphism of algebraic stacks
is quasi-compact and quasi-separated. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [QuasiSeparated f] :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S)
        (Hom.diagonal.{u + 1, u, u + 1} f) ∧
      Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
        (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

end QuasiSeparated

/-- The relative 2-diagonal of a morphism of algebraic stacks is representable
by algebraic spaces, so the scheme-slice tests above are well-defined. -/
theorem relativelyRepresentable_diagonal {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    relativelyRepresentableByAlgebraicSpaces
      (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
