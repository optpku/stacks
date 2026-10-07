module

public import stacks_project.Chap101.Definition_101_23_2_LocallyQuasiFinite
public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact
public import stacks_project.Chap67.Lemma_67_27_3_QuasiFinite

/-!
# Quasi-finite morphisms of algebraic stacks

A morphism of algebraic stacks is quasi-finite when it is locally
quasi-finite and quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism of algebraic stacks is quasi-finite if it is locally
quasi-finite and quasi-compact. -/
@[mk_iff]
class QuasiFinite {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop
    extends LocallyQuasiFinite f, QuasiCompact f

namespace QuasiFinite

/-- A quasi-finite morphism of algebraic stacks is locally quasi-finite and
quasi-compact. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [QuasiFinite f] :
    LocallyQuasiFinite f ∧ QuasiCompact f :=
  sorry

/-- The identity morphism of an algebraic stack is quasi-finite. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    QuasiFinite (𝟙 X) :=
  sorry

/-- An isomorphism of algebraic stacks is quasi-finite. -/
instance of_isIso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsIso f] :
    QuasiFinite f :=
  sorry

/-- A locally quasi-finite quasi-compact morphism of algebraic stacks is
quasi-finite. -/
instance instOfLocallyQuasiFiniteQuasiCompact {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [LocallyQuasiFinite f] [QuasiCompact f] : QuasiFinite f :=
  sorry

/-- A quasi-finite morphism of algebraic spaces induces a quasi-finite
1-morphism of algebraic stacks. -/
instance of_toGroupoids {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicSpace.QuasiFinite f] :
    QuasiFinite (AlgebraicSpace.toGroupoids.map f) :=
  sorry

end QuasiFinite

end AlgebraicGeometry.AlgebraicStack
