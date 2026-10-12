/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap78.Lemma_78_10_2_Equivariant
public import stacks_project.Chap78.Lemma_78_12_3_Pullback

/-!
# Pullback of equivariant quasi-coherent sheaves

An equivariant morphism `f : X ⟶ Y` of algebraic spaces with `G`-action induces a functor
from quasi-coherent `G`-equivariant sheaves on `Y` to those on `X`, by
`(F, α) ↦ (f* F, (1_G × f)* α)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- The map on arrows induced by an equivariant morphism between group algebraic space
actions. -/
def ofActionArrow (G : GroupAlgebraicSpace B) {X Y : GroupAlgebraicSpace.Action G}
    (f : X ⟶ Y) : (ofAction G X).R ⟶ (ofAction G Y).R :=
  G.X ◁ f.hom

/-- The arrow map induced by an equivariant morphism commutes with the source maps. -/
theorem ofActionArrow_source (G : GroupAlgebraicSpace B)
    {X Y : GroupAlgebraicSpace.Action G} (f : X ⟶ Y) :
    (ofAction G X).s ≫ f.hom = ofActionArrow G f ≫ (ofAction G Y).s :=
  sorry

/-- The arrow map induced by an equivariant morphism commutes with the target maps. -/
theorem ofActionArrow_target (G : GroupAlgebraicSpace B)
    {X Y : GroupAlgebraicSpace.Action G} (f : X ⟶ Y) :
    (ofAction G X).t ≫ f.hom = ofActionArrow G f ≫ (ofAction G Y).t :=
  sorry

/-- The arrow map induced by an equivariant morphism preserves groupoid composition. -/
theorem ofActionArrow_composition (G : GroupAlgebraicSpace B)
    {X Y : GroupAlgebraicSpace.Action G} (f : X ⟶ Y) :
    (ofAction G X).c ≫ ofActionArrow G f =
      composableMap f.hom (ofActionArrow G f)
          (ofActionArrow_source G f) (ofActionArrow_target G f) ≫
        (ofAction G Y).c :=
  sorry

/-- The morphism of action groupoids induced by a `G`-equivariant morphism. -/
def ofActionHom (G : GroupAlgebraicSpace B) {X Y : GroupAlgebraicSpace.Action G}
    (f : X ⟶ Y) : Hom (ofAction G X) (ofAction G Y) where
  obj := f.hom
  arrow := ofActionArrow G f
  map_s := ofActionArrow_source G f
  map_t := ofActionArrow_target G f
  map_c := ofActionArrow_composition G f

/-- The object component of the induced action-groupoid morphism is the given equivariant
morphism on underlying objects. -/
theorem ofActionHom_obj (G : GroupAlgebraicSpace B)
    {X Y : GroupAlgebraicSpace.Action G} (f : X ⟶ Y) :
    (ofActionHom G f).obj = f.hom :=
  sorry

/-- The arrow component of the induced action-groupoid morphism is the product of the
identity on the group algebraic space with the underlying object morphism. -/
theorem ofActionHom_arrow (G : GroupAlgebraicSpace B)
    {X Y : GroupAlgebraicSpace.Action G} (f : X ⟶ Y) :
    (ofActionHom G f).arrow = G.X ◁ f.hom :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.QCoh.Equivariant

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)

/-- The underlying algebraic-space morphism `1_G × f` induced by an equivariant morphism
`f`. -/
def oneProd {X Y : GroupAlgebraicSpace.Action G} (f : X ⟶ Y) :
    (G.X ⊗ X.X).left ⟶ (G.X ⊗ Y.X).left :=
  (GroupoidAlgebraicSpace.ofActionArrow G f).left

/-- The linearization on a pulled-back equivariant quasi-coherent sheaf, obtained by
pulling back the original linearization along `1_G × f`. -/
def pullbackAlpha {X Y : GroupAlgebraicSpace.Action G} (f : X ⟶ Y)
    (D : Equivariant G Y) :
    (AlgebraicSpace.QCoh.pullback (action G X)).obj
        ((AlgebraicSpace.QCoh.pullback f.hom.left).obj (obj D)) ⟶
      (AlgebraicSpace.QCoh.pullback (projection G X)).obj
        ((AlgebraicSpace.QCoh.pullback f.hom.left).obj (obj D)) :=
  GroupoidAlgebraicSpace.QCoh.pullbackAction (GroupoidAlgebraicSpace.ofActionHom G f) D

/-- Pullback along an equivariant morphism, as a functor on equivariant quasi-coherent
sheaves. -/
def pullback {X Y : GroupAlgebraicSpace.Action G} (f : X ⟶ Y) :
    Equivariant G Y ⥤ Equivariant G X :=
  GroupoidAlgebraicSpace.QCoh.pullback (GroupoidAlgebraicSpace.ofActionHom G f)

/-- The underlying module of equivariant pullback is ordinary quasi-coherent pullback. -/
theorem pullback_obj {X Y : GroupAlgebraicSpace.Action G} (f : X ⟶ Y)
    (D : Equivariant G Y) :
    obj ((pullback G f).obj D) =
      (AlgebraicSpace.QCoh.pullback f.hom.left).obj (obj D) :=
  sorry

/-- The linearization of equivariant pullback is the canonical pullback of the original
linearization along `1_G × f`. -/
theorem pullback_alpha {X Y : GroupAlgebraicSpace.Action G} (f : X ⟶ Y)
    (D : Equivariant G Y) :
    alpha ((pullback G f).obj D) = pullbackAlpha G f D :=
  sorry

/-- The underlying map of equivariant pullback is ordinary quasi-coherent pullback. -/
theorem pullback_map {X Y : GroupAlgebraicSpace.Action G} (f : X ⟶ Y)
    {A B : Equivariant G Y} (a : A ⟶ B) :
    hom ((pullback G f).map a) = (AlgebraicSpace.QCoh.pullback f.hom.left).map (hom a) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.QCoh.Equivariant
