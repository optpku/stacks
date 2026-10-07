module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import ReasLib.AlgebraicGeometry.GroupScheme
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Action
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import stacks_project.Chap78.Example_78_7_6_Constant_group_algebraic_space_Group
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap94.Definition_94_16_5_Quotient
public import stacks_project.Chap100.Lemma_100_11_3_LocallyNoetherian

/-!
# Quotient stacks of group scheme actions

A groupoid scheme over `S` determines a groupoid in algebraic spaces by
`ofOver`/`toBase`. The quotient stack `[X / G]` is the quotient of the action
groupoid; the classifying stack `BG` is the special case of the trivial action
on the terminal object of `Over (Spec (.of k))`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits
open MonoidalCategory CartesianMonoidalCategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- Comparison from the algebraic-space kernel pair of `ofOverSlice.map G.s` and
`ofOverSlice.map G.t` to `ofOver` of the scheme-level pullback. -/
def ofGroupoidScheme_kernelPair {S : Scheme.{u}} (G : GroupoidScheme S) :
    (pullback ((ConstantGroup.ofOverSlice S).map G.s)
        ((ConstantGroup.ofOverSlice S).map G.t)).left ⟶
      ofOver (pullback G.s G.t) :=
  let source := (ConstantGroup.ofOverSlice S).map G.s
  let target := (ConstantGroup.ofOverSlice S).map G.t
  let toPresheafPullback :
      (pullback source target).left.functorOfPoints ⟶
        pullback (yoneda.map G.s) (yoneda.map G.t) :=
    pullback.lift (pullback.fst source target).left (pullback.snd source target).left sorry
  (toPresheafPullback ≫ (PreservesPullback.iso yoneda G.s G.t).inv :
    (pullback source target).left.functorOfPoints ⟶
      (ofOver (pullback G.s G.t)).functorOfPoints)

/-- The composition morphism of a groupoid scheme, as a morphism of algebraic
spaces out of the kernel pair of the converted source and target. -/
def ofGroupoidScheme_compose {S : Scheme.{u}} (G : GroupoidScheme S) :
    pullback ((ConstantGroup.ofOverSlice S).map G.s)
      ((ConstantGroup.ofOverSlice S).map G.t) ⟶
      (ConstantGroup.ofOverSlice S).obj G.R :=
  Over.homMk (ofGroupoidScheme_kernelPair G ≫ ofOverMap G.c) sorry

/-- A groupoid scheme over `S`, regarded as a groupoid in algebraic spaces over
`S` by applying `ConstantGroup.ofOverSlice` to objects, arrows, and structure
maps, with composition transported along `ofGroupoidScheme_kernelPair`. -/
def ofGroupoidScheme {S : Scheme.{u}} (G : GroupoidScheme S) :
    GroupoidAlgebraicSpace (ofOver (Over.mk (𝟙 S))) where
  U := (ConstantGroup.ofOverSlice S).obj G.U
  R := (ConstantGroup.ofOverSlice S).obj G.R
  s := (ConstantGroup.ofOverSlice S).map G.s
  t := (ConstantGroup.ofOverSlice S).map G.t
  c := ofGroupoidScheme_compose G
  e := (ConstantGroup.ofOverSlice S).map G.e
  i := (ConstantGroup.ofOverSlice S).map G.i
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

/-- The object space of `ofGroupoidScheme G` is `ofOver` of the object scheme. -/
theorem ofGroupoidScheme_U {S : Scheme.{u}} (G : GroupoidScheme S) :
    (ofGroupoidScheme G).U.left = ofOver G.U := sorry

/-- The arrow space of `ofGroupoidScheme G` is `ofOver` of the arrow scheme. -/
theorem ofGroupoidScheme_R {S : Scheme.{u}} (G : GroupoidScheme S) :
    (ofGroupoidScheme G).R.left = ofOver G.R := sorry

/-- The source of `ofGroupoidScheme G` is `ofOverMap` of the source of `G`. -/
theorem ofGroupoidScheme_s {S : Scheme.{u}} (G : GroupoidScheme S) :
    (ofGroupoidScheme G).s.left = ofOverMap G.s := sorry

/-- The target of `ofGroupoidScheme G` is `ofOverMap` of the target of `G`. -/
theorem ofGroupoidScheme_t {S : Scheme.{u}} (G : GroupoidScheme S) :
    (ofGroupoidScheme G).t.left = ofOverMap G.t := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace

namespace AlgebraicGeometry.GroupScheme

/-- The trivial action of a group scheme `G` on the terminal object of `Over S`. -/
def trivialAction {S : Scheme.{u}} (G : GroupScheme S) : Action G :=
  Mod.trivialAction G.toMon (𝟙_ (Over S))

/-- The underlying object of `trivialAction G` is the terminal scheme over `S`. -/
theorem trivialAction_X {S : Scheme.{u}} (G : GroupScheme S) :
    (trivialAction G).X = 𝟙_ (Over S) := sorry

end AlgebraicGeometry.GroupScheme

namespace AlgebraicGeometry

/-- The terminal scheme over `Spec (.of k)` is algebraic over `k`. -/
instance instAlgebraic_overField_terminal {k : Type u} [Field k] :
    Algebraic (𝟙_ (Over (Spec (.of k)))) := sorry

end AlgebraicGeometry

namespace AlgebraicGeometry.AlgebraicStack

/-- The quotient stack `[X / G]` of a group scheme acting on a scheme over a
field, obtained by converting the action groupoid to algebraic spaces and
stackifying. -/
def quotient {k : Type u} [Field k] (G : GroupScheme (Spec (.of k)))
    (X : GroupScheme.Action G) : GroupoidsOver (Spec (.of k)) :=
  (GroupoidAlgebraicSpace.ofGroupoidScheme (GroupoidScheme.ofAction G X)).quotientStack

/-- `quotient G X` is the quotient stack of the converted action groupoid. -/
theorem quotient_spec {k : Type u} [Field k] (G : GroupScheme (Spec (.of k)))
    (X : GroupScheme.Action G) :
    quotient G X =
      (GroupoidAlgebraicSpace.ofGroupoidScheme
        (GroupoidScheme.ofAction G X)).quotientStack := sorry

/-- The classifying stack `BG = [Spec k / G]` is the quotient by the trivial
action on the terminal object of `Over (Spec (.of k))`. -/
def classifying {k : Type u} [Field k] (G : GroupScheme (Spec (.of k))) :
    GroupoidsOver (Spec (.of k)) :=
  quotient G (GroupScheme.trivialAction G)

/-- `classifying G` is the quotient stack of the trivial action of `G`. -/
theorem classifying_spec {k : Type u} [Field k] (G : GroupScheme (Spec (.of k))) :
    classifying G = quotient G (GroupScheme.trivialAction G) := sorry

/-- The quotient stack of a finite-type group scheme action over a field is an
algebraic stack. -/
instance instAlgebraicStack_quotient {k : Type u} [Field k]
    (G : GroupScheme (Spec (.of k))) (X : GroupScheme.Action G)
    [Algebraic X.X] [Algebraic G.X] : AlgebraicStack (quotient G X) := sorry

/-- The quotient stack of a finite-type group scheme action over a field is
locally Noetherian. -/
instance instIsLocallyNoetherian_quotient {k : Type u} [Field k]
    (G : GroupScheme (Spec (.of k))) (X : GroupScheme.Action G)
    [Algebraic X.X] [Algebraic G.X] : IsLocallyNoetherian (quotient G X) := sorry

/-- The classifying stack of a finite-type group scheme over a field is an
algebraic stack. -/
instance instAlgebraicStack_classifying {k : Type u} [Field k]
    (G : GroupScheme (Spec (.of k))) [Algebraic G.X] :
    AlgebraicStack (classifying G) := sorry

/-- The classifying stack of a finite-type group scheme over a field is locally
Noetherian. -/
instance instIsLocallyNoetherian_classifying {k : Type u} [Field k]
    (G : GroupScheme (Spec (.of k))) [Algebraic G.X] :
    IsLocallyNoetherian (classifying G) := sorry

end AlgebraicGeometry.AlgebraicStack
