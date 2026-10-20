module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import ReasLib.AlgebraicGeometry.GroupoidScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.Representable

/-!
# Groupoid schemes as groupoids in algebraic spaces

A groupoid scheme over `S` determines a groupoid in algebraic spaces over `S`
by applying `ofOver` to the object scheme, arrow scheme, and structure maps.
The represented endpoints are transparent to inference, so morphism properties
transfer through the generic instances for represented scheme morphisms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

open AlgebraicGeometry.AlgebraicSpace

/-- The object scheme of a groupoid scheme, as an algebraic space over `S`. -/
@[reducible]
def objectOver {S : Scheme.{u}} (G : GroupoidScheme S) :
    Over (ofOver (Over.mk (𝟙 S))) :=
  { left := ofOver G.U
    right := Discrete.mk PUnit.unit
    hom := SchemeRealization.toBase (ofOver G.U) }

/-- The arrow scheme of a groupoid scheme, as an algebraic space over `S`. -/
@[reducible]
def arrowOver {S : Scheme.{u}} (G : GroupoidScheme S) :
    Over (ofOver (Over.mk (𝟙 S))) :=
  { left := ofOver G.R
    right := Discrete.mk PUnit.unit
    hom := SchemeRealization.toBase (ofOver G.R) }

/-- The source morphism of a groupoid scheme, as a morphism of algebraic spaces. -/
@[reducible]
def sourceOver {S : Scheme.{u}} (G : GroupoidScheme S) :
    arrowOver G ⟶ objectOver G :=
  { left := ofOverMap G.s
    right := 𝟙 _
    w := by
      change ofOverMap G.s ≫ SchemeRealization.toBase (ofOver G.U) =
        SchemeRealization.toBase (ofOver G.R) ≫ 𝟙 _
      simpa only [Category.comp_id] using
        SchemeRealization.eq_toBase (ofOverMap G.s ≫ SchemeRealization.toBase (ofOver G.U)) }

/-- The target morphism of a groupoid scheme, as a morphism of algebraic spaces. -/
@[reducible]
def targetOver {S : Scheme.{u}} (G : GroupoidScheme S) :
    arrowOver G ⟶ objectOver G :=
  { left := ofOverMap G.t
    right := 𝟙 _
    w := by
      change ofOverMap G.t ≫ SchemeRealization.toBase (ofOver G.U) =
        SchemeRealization.toBase (ofOver G.R) ≫ 𝟙 _
      simpa only [Category.comp_id] using
        SchemeRealization.eq_toBase (ofOverMap G.t ≫ SchemeRealization.toBase (ofOver G.U)) }

/-- The identity-arrow morphism of a groupoid scheme, as a morphism of algebraic
spaces. -/
def identityOver {S : Scheme.{u}} (G : GroupoidScheme S) :
    objectOver G ⟶ arrowOver G :=
  Over.homMk (ofOverMap G.e)
    (SchemeRealization.eq_toBase (ofOverMap G.e ≫ SchemeRealization.toBase (ofOver G.R)))

/-- The inverse-arrow morphism of a groupoid scheme, as a morphism of algebraic
spaces. -/
def inverseOver {S : Scheme.{u}} (G : GroupoidScheme S) :
    arrowOver G ⟶ arrowOver G :=
  Over.homMk (ofOverMap G.i)
    (SchemeRealization.eq_toBase (ofOverMap G.i ≫ SchemeRealization.toBase (ofOver G.R)))

/-- The two projections of the algebraic-space kernel pair commute with source
and target. -/
private theorem kernelPairToOfOver_condition {S : Scheme.{u}} (G : GroupoidScheme S) :
    (pullback.fst (sourceOver G) (targetOver G)).left ≫ ofOverMap G.s =
      (pullback.snd (sourceOver G) (targetOver G)).left ≫ ofOverMap G.t :=
  sorry

/-- Comparison from the algebraic-space kernel pair of `sourceOver` and
`targetOver` to `ofOver` of the scheme-theoretic fibre product. -/
def kernelPairToOfOver {S : Scheme.{u}} (G : GroupoidScheme S) :
    (pullback (sourceOver G) (targetOver G)).left ⟶ ofOver (pullback G.s G.t) :=
  ((pullback.lift (pullback.fst (sourceOver G) (targetOver G)).left
        (pullback.snd (sourceOver G) (targetOver G)).left
        (by exact kernelPairToOfOver_condition G) :
      (pullback (sourceOver G) (targetOver G)).left.functorOfPoints ⟶
        pullback (yoneda.map G.s) (yoneda.map G.t)) ≫
      (PreservesPullback.iso yoneda G.s G.t).inv :
    (pullback (sourceOver G) (targetOver G)).left.functorOfPoints ⟶
      (ofOver (pullback G.s G.t)).functorOfPoints)

/-- The composition morphism of a groupoid scheme lies over `S` as an algebraic
space. -/
private theorem composeOver_w {S : Scheme.{u}} (G : GroupoidScheme S) :
    (kernelPairToOfOver G ≫ ofOverMap G.c) ≫ (arrowOver G).hom =
      (pullback (sourceOver G) (targetOver G)).hom :=
  sorry

/-- The composition morphism of a groupoid scheme, as a morphism of algebraic
spaces out of the kernel pair. -/
def composeOver {S : Scheme.{u}} (G : GroupoidScheme S) :
    pullback (sourceOver G) (targetOver G) ⟶ arrowOver G :=
  Over.homMk (kernelPairToOfOver G ≫ ofOverMap G.c) (by exact composeOver_w G)

/-- The source of a composite is the source of its earlier arrow. -/
private theorem ofScheme_comp_source {S : Scheme.{u}} (G : GroupoidScheme S) :
    (composeOver G) ≫ (sourceOver G) = pullback.snd (sourceOver G) (targetOver G) ≫ (sourceOver G) :=
  sorry

/-- The target of a composite is the target of its later arrow. -/
private theorem ofScheme_comp_target {S : Scheme.{u}} (G : GroupoidScheme S) :
    (composeOver G) ≫ (targetOver G) = pullback.fst (sourceOver G) (targetOver G) ≫ (targetOver G) :=
  sorry

/-- Identity arrows have the specified source. -/
private theorem ofScheme_identity_source {S : Scheme.{u}} (G : GroupoidScheme S) :
    (identityOver G) ≫ (sourceOver G) = 𝟙 (objectOver G) :=
  sorry

/-- Identity arrows have the specified target. -/
private theorem ofScheme_identity_target {S : Scheme.{u}} (G : GroupoidScheme S) :
    (identityOver G) ≫ (targetOver G) = 𝟙 (objectOver G) :=
  sorry

/-- Inversion exchanges source with target. -/
private theorem ofScheme_inverse_source {S : Scheme.{u}} (G : GroupoidScheme S) :
    (inverseOver G) ≫ (sourceOver G) = (targetOver G) :=
  sorry

/-- Inversion exchanges target with source. -/
private theorem ofScheme_inverse_target {S : Scheme.{u}} (G : GroupoidScheme S) :
    (inverseOver G) ≫ (targetOver G) = (sourceOver G) :=
  sorry

/-- Composition of represented arrows is associative on every object of points over the base. -/
private theorem ofScheme_associativity {S : Scheme.{u}} (G : GroupoidScheme S) :
    ∀ {T : Over (ofOver (Over.mk (𝟙 S)))} (a b d : T ⟶ (arrowOver G))
      (h_ab : a ≫ (sourceOver G) = b ≫ (targetOver G)) (h_bd : b ≫ (sourceOver G) = d ≫ (targetOver G))
      (h_ab_d : (pullback.lift a b h_ab ≫ (composeOver G)) ≫ (sourceOver G) = d ≫ (targetOver G))
      (h_a_bd : a ≫ (sourceOver G) = (pullback.lift b d h_bd ≫ (composeOver G)) ≫ (targetOver G)),
      pullback.lift (pullback.lift a b h_ab ≫ (composeOver G)) d h_ab_d ≫ (composeOver G) =
        pullback.lift a (pullback.lift b d h_bd ≫ (composeOver G)) h_a_bd ≫ (composeOver G) :=
  sorry

/-- Composing an arrow with the identity at its source does not change it. -/
private theorem ofScheme_right_identity {S : Scheme.{u}} (G : GroupoidScheme S) :
    ∀ {T : Over (ofOver (Over.mk (𝟙 S)))} (a : T ⟶ (arrowOver G))
      (h : a ≫ (sourceOver G) = ((a ≫ (sourceOver G)) ≫ (identityOver G)) ≫ (targetOver G)),
      pullback.lift a ((a ≫ (sourceOver G)) ≫ (identityOver G)) h ≫ (composeOver G) = a :=
  sorry

/-- Composing the identity at the target of an arrow with that arrow does not change it. -/
private theorem ofScheme_left_identity {S : Scheme.{u}} (G : GroupoidScheme S) :
    ∀ {T : Over (ofOver (Over.mk (𝟙 S)))} (a : T ⟶ (arrowOver G))
      (h : ((a ≫ (targetOver G)) ≫ (identityOver G)) ≫ (sourceOver G) = a ≫ (targetOver G)),
      pullback.lift ((a ≫ (targetOver G)) ≫ (identityOver G)) a h ≫ (composeOver G) = a :=
  sorry

/-- Composing an arrow after its inverse gives the identity at its target. -/
private theorem ofScheme_inverse_comp {S : Scheme.{u}} (G : GroupoidScheme S) :
    ∀ {T : Over (ofOver (Over.mk (𝟙 S)))} (a : T ⟶ (arrowOver G))
      (h : a ≫ (sourceOver G) = (a ≫ (inverseOver G)) ≫ (targetOver G)),
      pullback.lift a (a ≫ (inverseOver G)) h ≫ (composeOver G) = (a ≫ (targetOver G)) ≫ (identityOver G) :=
  sorry

/-- Composing the inverse of an arrow after it gives the identity at its source. -/
private theorem ofScheme_comp_inverse {S : Scheme.{u}} (G : GroupoidScheme S) :
    ∀ {T : Over (ofOver (Over.mk (𝟙 S)))} (a : T ⟶ (arrowOver G))
      (h : (a ≫ (inverseOver G)) ≫ (sourceOver G) = a ≫ (targetOver G)),
      pullback.lift (a ≫ (inverseOver G)) a h ≫ (composeOver G) = (a ≫ (sourceOver G)) ≫ (identityOver G) :=
  sorry

/-- A groupoid scheme over `S`, regarded as a groupoid in algebraic spaces over
`S` by applying `ofOver` to objects, arrows, and structure maps. -/
@[reducible]
def ofScheme {S : Scheme.{u}} (G : GroupoidScheme S) :
    GroupoidAlgebraicSpace (ofOver (Over.mk (𝟙 S))) where
  U := objectOver G
  R := arrowOver G
  s := sourceOver G
  t := targetOver G
  c := composeOver G
  e := identityOver G
  i := inverseOver G
  comp_source := by exact ofScheme_comp_source G
  comp_target := by exact ofScheme_comp_target G
  identity_source := by exact ofScheme_identity_source G
  identity_target := by exact ofScheme_identity_target G
  inverse_source := by exact ofScheme_inverse_source G
  inverse_target := by exact ofScheme_inverse_target G
  associativity := by exact ofScheme_associativity G
  right_identity := by exact ofScheme_right_identity G
  left_identity := by exact ofScheme_left_identity G
  inverse_comp := by exact ofScheme_inverse_comp G
  comp_inverse := by exact ofScheme_comp_inverse G

/-- The object space of `ofScheme G` is `ofOver` of the object scheme. -/
theorem ofScheme_U {S : Scheme.{u}} (G : GroupoidScheme S) :
    (ofScheme G).U.left = ofOver G.U :=
  rfl

/-- The arrow space of `ofScheme G` is `ofOver` of the arrow scheme. -/
theorem ofScheme_R {S : Scheme.{u}} (G : GroupoidScheme S) :
    (ofScheme G).R.left = ofOver G.R :=
  rfl

end AlgebraicGeometry.GroupoidAlgebraicSpace
