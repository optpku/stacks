module

public import stacks_project.Chap67.Lemma_67_38_5_Unramified
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap101.Lemma_101_21_1
public import stacks_project.Chap101.Lemma_101_36_4_Etale

/-!
# Shrinking a flat locally finitely presented morphism to an étale morphism

An unramified point of a cartesian field fibre of a flat, locally finitely
presented morphism from an algebraic space to an algebraic stack lies in an
open subspace on which the restricted morphism is étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The projection `F ⟶ Spec(k)` of a cartesian field fibre, recovered from an
algebraic-space model of `TwoFibreProduct.apex f p.hom`. -/
def representedFiberToSpec {S : Scheme.{u}} {U : AlgebraicSpace S}
    {X : GroupoidsOver S} {f : U.toGroupoids ⟶ X} {p : FieldValuedPoint X}
    {F : AlgebraicSpace S}
    (e : TwoFibreProduct.apex.{u + 1, u, u + 1, u} f p.hom ≌ F.toGroupoids) :
    F ⟶ AlgebraicSpace.ofOver p.overObj :=
  AlgebraicSpace.toGroupoids.eval
    (e.inv ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f p.hom ≫
      (AlgebraicSpace.ofOverSliceEquiv p.overObj).inv)

/-- `representedFiberToSpec e` is the morphism of algebraic spaces recovered from
`e.inv ≫ TwoFibreProduct.snd f p.hom ≫ (ofOverSliceEquiv p.overObj).inv`. -/
theorem representedFiberToSpec_eq {S : Scheme.{u}} {U : AlgebraicSpace S}
    {X : GroupoidsOver S} {f : U.toGroupoids ⟶ X} {p : FieldValuedPoint X}
    {F : AlgebraicSpace S}
    (e : TwoFibreProduct.apex.{u + 1, u, u + 1, u} f p.hom ≌ F.toGroupoids) :
    representedFiberToSpec e =
      AlgebraicSpace.toGroupoids.eval
        (e.inv ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f p.hom ≫
          (AlgebraicSpace.ofOverSliceEquiv p.overObj).inv) :=
  sorry

/-- The restricted morphism `W.X ⟶ X` obtained by composing the inclusion of an
open subspace of `U` with `f : U.toGroupoids ⟶ X`. -/
def openSubspaceToStack {S : Scheme.{u}} {U : AlgebraicSpace S}
    {X : GroupoidsOver S} (f : U.toGroupoids ⟶ X)
    (W : AlgebraicSpace.OpenSubspace U) : W.X.toGroupoids ⟶ X :=
  AlgebraicSpace.toGroupoids.map W.ι ≫ f

/-- `openSubspaceToStack f W` is `toGroupoids.map W.ι ≫ f`. -/
theorem openSubspaceToStack_eq {S : Scheme.{u}} {U : AlgebraicSpace S}
    {X : GroupoidsOver S} (f : U.toGroupoids ⟶ X)
    (W : AlgebraicSpace.OpenSubspace U) :
    openSubspaceToStack f W = AlgebraicSpace.toGroupoids.map W.ι ≫ f :=
  sorry

/-- Lemma 101.21.5: Let `X` be an algebraic stack. Consider a cartesian diagram
where `U` is an algebraic space, `k` is a field, and `U ⟶ X` is flat and
locally of finite presentation. Let `z` be a point of an algebraic-space model
`F` of the cartesian field fibre `U ×_X Spec(k)` such that `F ⟶ Spec(k)` is
unramified at `z`. Then after replacing `U` by an open subspace containing the
image of `z` in `|U|`, the morphism `U ⟶ X` is étale. -/
@[stacks 06N2]
theorem exists_openSubspace_etale {S : Scheme.{u}} {U : AlgebraicSpace S}
    {X : GroupoidsOver S} [AlgebraicStack X] (f : U.toGroupoids ⟶ X)
    [Flat f] [LocallyOfFinitePresentation f] (p : FieldValuedPoint X)
    {F : AlgebraicSpace S}
    (e : TwoFibreProduct.apex.{u + 1, u, u + 1, u} f p.hom ≌ F.toGroupoids)
    (z : AlgebraicSpace.Points F)
    (h_unramified : AlgebraicSpace.UnramifiedAt (representedFiberToSpec e) z) :
    ∃ W : AlgebraicSpace.OpenSubspace U,
      AlgebraicSpace.Points.map (representedFiberι e) z ∈ W.pointsSet ∧
        Etale (openSubspaceToStack f W) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
