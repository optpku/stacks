module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import ReasLib.AlgebraicGeometry.GroupoidScheme
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_4_13
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap78.Definition_78_11_1_Groupoid

/-!
# Groupoid schemes as groupoids in algebraic spaces

A groupoid scheme over `S` determines a groupoid in algebraic spaces over `S`
by applying `ofOver` to the object scheme, arrow scheme, and structure maps.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

open AlgebraicGeometry.AlgebraicSpace

/-- The object scheme of a groupoid scheme, as an algebraic space over `S`. -/
def objectOver {S : Scheme.{u}} (G : GroupoidScheme S) :
    Over (ofOver (Over.mk (𝟙 S))) :=
  Over.mk (toBase (ofOver G.U))

/-- The arrow scheme of a groupoid scheme, as an algebraic space over `S`. -/
def arrowOver {S : Scheme.{u}} (G : GroupoidScheme S) :
    Over (ofOver (Over.mk (𝟙 S))) :=
  Over.mk (toBase (ofOver G.R))

/-- The source morphism of a groupoid scheme, as a morphism of algebraic spaces. -/
def sourceOver {S : Scheme.{u}} (G : GroupoidScheme S) :
    arrowOver G ⟶ objectOver G :=
  Over.homMk (ofOverMap G.s) (eq_toBase (ofOverMap G.s ≫ toBase (ofOver G.U)))

/-- The target morphism of a groupoid scheme, as a morphism of algebraic spaces. -/
def targetOver {S : Scheme.{u}} (G : GroupoidScheme S) :
    arrowOver G ⟶ objectOver G :=
  Over.homMk (ofOverMap G.t) (eq_toBase (ofOverMap G.t ≫ toBase (ofOver G.U)))

/-- The identity-arrow morphism of a groupoid scheme, as a morphism of algebraic
spaces. -/
def identityOver {S : Scheme.{u}} (G : GroupoidScheme S) :
    objectOver G ⟶ arrowOver G :=
  Over.homMk (ofOverMap G.e) (eq_toBase (ofOverMap G.e ≫ toBase (ofOver G.R)))

/-- The inverse-arrow morphism of a groupoid scheme, as a morphism of algebraic
spaces. -/
def inverseOver {S : Scheme.{u}} (G : GroupoidScheme S) :
    arrowOver G ⟶ arrowOver G :=
  Over.homMk (ofOverMap G.i) (eq_toBase (ofOverMap G.i ≫ toBase (ofOver G.R)))

/-- The two projections of the algebraic-space kernel pair commute with source
and target. -/
theorem kernelPairToOfOver_condition {S : Scheme.{u}} (G : GroupoidScheme S) :
    (pullback.fst (sourceOver G) (targetOver G)).left ≫ ofOverMap G.s =
      (pullback.snd (sourceOver G) (targetOver G)).left ≫ ofOverMap G.t :=
  sorry

/-- Comparison from the algebraic-space kernel pair of `sourceOver` and
`targetOver` to `ofOver` of the scheme-theoretic fibre product. -/
def kernelPairToOfOver {S : Scheme.{u}} (G : GroupoidScheme S) :
    (pullback (sourceOver G) (targetOver G)).left ⟶ ofOver (pullback G.s G.t) :=
  ((pullback.lift (pullback.fst (sourceOver G) (targetOver G)).left
        (pullback.snd (sourceOver G) (targetOver G)).left
        (kernelPairToOfOver_condition G) :
      (pullback (sourceOver G) (targetOver G)).left.functorOfPoints ⟶
        pullback (yoneda.map G.s) (yoneda.map G.t)) ≫
      (PreservesPullback.iso yoneda G.s G.t).inv :
    (pullback (sourceOver G) (targetOver G)).left.functorOfPoints ⟶
      (ofOver (pullback G.s G.t)).functorOfPoints)

/-- The composition morphism of a groupoid scheme lies over `S` as an algebraic
space. -/
theorem composeOver_w {S : Scheme.{u}} (G : GroupoidScheme S) :
    (kernelPairToOfOver G ≫ ofOverMap G.c) ≫ (arrowOver G).hom =
      (pullback (sourceOver G) (targetOver G)).hom :=
  sorry

/-- The composition morphism of a groupoid scheme, as a morphism of algebraic
spaces out of the kernel pair. -/
def composeOver {S : Scheme.{u}} (G : GroupoidScheme S) :
    pullback (sourceOver G) (targetOver G) ⟶ arrowOver G :=
  Over.homMk (kernelPairToOfOver G ≫ ofOverMap G.c) (composeOver_w G)

/-- A groupoid scheme over `S`, regarded as a groupoid in algebraic spaces over
`S` by applying `ofOver` to objects, arrows, and structure maps. -/
def ofScheme {S : Scheme.{u}} (G : GroupoidScheme S) :
    GroupoidAlgebraicSpace (ofOver (Over.mk (𝟙 S))) where
  U := objectOver G
  R := arrowOver G
  s := sourceOver G
  t := targetOver G
  c := composeOver G
  e := identityOver G
  i := inverseOver G
  comp_source := sorry
  comp_target := sorry
  identity_source := sorry
  identity_target := sorry
  inverse_source := sorry
  inverse_target := sorry
  associativity := sorry
  right_identity := sorry
  left_identity := sorry
  inverse_comp := sorry
  comp_inverse := sorry

/-- The object space of `ofScheme G` is `ofOver` of the object scheme. -/
theorem ofScheme_U {S : Scheme.{u}} (G : GroupoidScheme S) :
    (ofScheme G).U.left = ofOver G.U :=
  rfl

/-- The arrow space of `ofScheme G` is `ofOver` of the arrow scheme. -/
theorem ofScheme_R {S : Scheme.{u}} (G : GroupoidScheme S) :
    (ofScheme G).R.left = ofOver G.R :=
  rfl

/-- Separatedness of the source of a groupoid scheme transfers to `ofScheme`. -/
instance ofScheme_source_separated {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsSeparated G.s.left] : AlgebraicSpace.Separated (ofScheme G).s.left :=
  (separated_ofOverMap_iff G.s).mpr inferInstance

/-- Separatedness of the target of a groupoid scheme transfers to `ofScheme`. -/
instance ofScheme_target_separated {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsSeparated G.t.left] : AlgebraicSpace.Separated (ofScheme G).t.left :=
  (separated_ofOverMap_iff G.t).mpr inferInstance

/-- Local finite type of the source of a groupoid scheme transfers to `ofScheme`. -/
instance ofScheme_source_locallyOfFiniteType {S : Scheme.{u}} (G : GroupoidScheme S)
    [AlgebraicGeometry.LocallyOfFiniteType G.s.left] :
    AlgebraicSpace.LocallyOfFiniteType (ofScheme G).s.left :=
  sorry

/-- Local finite type of the target of a groupoid scheme transfers to `ofScheme`. -/
instance ofScheme_target_locallyOfFiniteType {S : Scheme.{u}} (G : GroupoidScheme S)
    [AlgebraicGeometry.LocallyOfFiniteType G.t.left] :
    AlgebraicSpace.LocallyOfFiniteType (ofScheme G).t.left :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
