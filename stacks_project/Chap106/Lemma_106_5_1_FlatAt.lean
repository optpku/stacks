module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap100.Lemma_100_7_4_Points
public import stacks_project.Chap101.Lemma_101_25_5_Flat

/-!
# Flatness at a point for morphisms of algebraic stacks

A morphism of algebraic stacks is flat at a source point when some algebraic
space square over it has flat target atlas, flat comparison into the 2-fibre
product, and top arrow flat at a germ mapping to that point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism of algebraic stacks is flat at a point of the source when some
algebraic-space square over it has flat target atlas, the comparison into the
2-fibre product is flat, and the top arrow is flat at a germ mapping to that
point. -/
def FlatAt {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (x : Points X) : Prop :=
  ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
    (h : U ⟶ V) (u : AlgebraicSpace.Points U)
    (φ : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} b f),
    Nonempty (a ≫ f ≅ AlgebraicSpace.toGroupoids.map h ≫ b) ∧
      Flat b ∧ Groupoids.Hom.Flat φ ∧
        Nonempty
            (φ ≫ TwoFibreProduct.fst.{u + 1, u, u + 1, u} b f ≅
              AlgebraicSpace.toGroupoids.map h) ∧
          Nonempty (φ ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} b f ≅ a) ∧
            Points.mapSpace a u = x ∧ AlgebraicSpace.FlatAt h u

/-- Flatness at a point is equivalent to the existence of an algebraic-space
presentation square whose target atlas is flat, whose comparison into the
2-fibre product is flat, and whose top arrow is flat at a germ mapping to that
point. -/
theorem flatAt_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (x : Points X) :
    FlatAt f x ↔
      ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
        (h : U ⟶ V) (u : AlgebraicSpace.Points U)
        (φ : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} b f),
        Nonempty (a ≫ f ≅ AlgebraicSpace.toGroupoids.map h ≫ b) ∧
          Flat b ∧ Groupoids.Hom.Flat φ ∧
            Nonempty
                (φ ≫ TwoFibreProduct.fst.{u + 1, u, u + 1, u} b f ≅
                  AlgebraicSpace.toGroupoids.map h) ∧
              Nonempty (φ ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} b f ≅ a) ∧
                Points.mapSpace a u = x ∧ AlgebraicSpace.FlatAt h u :=
  sorry

end AlgebraicGeometry.AlgebraicStack
