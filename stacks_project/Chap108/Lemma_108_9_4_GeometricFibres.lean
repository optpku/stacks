/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_19_1_GeometricPoint
public import stacks_project.Chap68.Lemma_68_18_6_Fibre
public import stacks_project.Chap72.Definition_72_4_1_Integral

/-!
# Morphisms of algebraic spaces with integral geometric fibres

A morphism of algebraic spaces has integral geometric fibres when every
geometric fibre is an integral algebraic space.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- A morphism of algebraic spaces has integral geometric fibres if the fibre over
every geometric point of the target is integral. -/
@[mk_iff]
class HasIntegralGeometricFibres {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop where
  /-- The geometric fibre over every geometric point of the target is integral. -/
  isIntegral_geometricFiber (ybar : GeometricPoint Y) :
    IsIntegral (fieldFiber f ybar.toFieldValuedPoint)

namespace HasIntegralGeometricFibres

/-- A morphism with integral geometric fibres has an integral geometric fibre over
every geometric point of the target. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [HasIntegralGeometricFibres f] (ybar : GeometricPoint Y) :
    IsIntegral (fieldFiber f ybar.toFieldValuedPoint) :=
  sorry

/-- Integrality of every geometric fibre witnesses that a morphism of algebraic
spaces has integral geometric fibres. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (h : ∀ ybar : GeometricPoint Y,
      IsIntegral (fieldFiber f ybar.toFieldValuedPoint)) :
    HasIntegralGeometricFibres f :=
  sorry

/-- Having integral geometric fibres is equivalent to every geometric fibre being
an integral algebraic space. -/
theorem iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    HasIntegralGeometricFibres f ↔
      ∀ ybar : GeometricPoint Y,
        IsIntegral (fieldFiber f ybar.toFieldValuedPoint) :=
  sorry

end HasIntegralGeometricFibres

/-- The identity morphism of an algebraic space has integral geometric fibres. -/
instance instHasIntegralGeometricFibres_id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    HasIntegralGeometricFibres (𝟙 X) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
