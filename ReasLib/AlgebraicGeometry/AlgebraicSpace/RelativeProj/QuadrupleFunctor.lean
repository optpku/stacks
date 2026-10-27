/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Logic.Equiv.Sum
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OfRepresentable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.Quadruple

/-!
# Size-safe relative projective functors of algebraic spaces

The functor `F` of equivalence classes of relative projective quadruples is recorded as a
size-safe functor over the functor of points of the base algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

/-- A size-safe relative projective functor over the functor of points of an algebraic space. -/
structure ProjFunctor {S : Scheme.{u}} (X : AlgebraicSpace S)
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)) where
  /-- The functor on schemes over `S` underlying `F`. -/
  toFunctor : (Over S)ᵒᵖ ⥤ Type u
  /-- The structural map to the functor of points of the base algebraic space. -/
  baseMap : toFunctor ⟶ X.functorOfPoints
  /-- Every graded piece of the underlying algebra sheaf is quasicoherent. -/
  algebra_isQuasicoherent : 𝒜.IsQuasicoherent
  /-- Multiplication in the graded algebra is ordinarily commutative. -/
  algebra_isCommutative : 𝒜.IsCommutative

/-- Construct a relative projective functor from a functor over `X.functorOfPoints` and
quasicoherence of `𝒜`. -/
def ProjFunctor.ofFunctor {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (toFunctor : (Over S)ᵒᵖ ⥤ Type u) (baseMap : toFunctor ⟶ X.functorOfPoints)
    (algebra_isQuasicoherent : 𝒜.IsQuasicoherent)
    (algebra_isCommutative : 𝒜.IsCommutative) :
    ProjFunctor X 𝒜 where
  toFunctor := toFunctor
  baseMap := baseMap
  algebra_isQuasicoherent := algebra_isQuasicoherent
  algebra_isCommutative := algebra_isCommutative


/-- The graded algebra underlying a relative projective functor is quasicoherent and
ordinarily commutative. -/
theorem ProjFunctor.conditions_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (F : ProjFunctor X 𝒜) :
    𝒜.IsQuasicoherent ∧ 𝒜.IsCommutative :=
  ⟨F.algebra_isQuasicoherent, F.algebra_isCommutative⟩

/-- The object of `Over S` obtained by restricting a scheme over `S` to a Zariski open. -/
def openOver {S : Scheme.{u}} (T : Over S) (V : T.left.Opens) : Over S :=
  Over.mk (V.ι ≫ T.hom)

/-- The structure morphism of `openOver T V` is the open immersion followed by `T.hom`. -/
theorem openOver_hom {S : Scheme.{u}} (T : Over S) (V : T.left.Opens) :
    (openOver T V).hom = V.ι ≫ T.hom :=
  rfl

/-- The open immersion `openOver T V ⟶ T` in `Over S`. -/
def openOverι {S : Scheme.{u}} (T : Over S) (V : T.left.Opens) :
    openOver T V ⟶ T :=
  Over.homMk V.ι rfl

/-- The left component of `openOverι T V` is the open immersion of `V`. -/
theorem openOverι_left {S : Scheme.{u}} (T : Over S) (V : T.left.Opens) :
    (openOverι T V).left = V.ι :=
  rfl

/-- The underlying scheme of `openOver T V` is the open subscheme `V`. -/
theorem openOver_left {S : Scheme.{u}} (T : Over S) (V : T.left.Opens) :
    (openOver T V).left = V.toScheme :=
  rfl

/-- Quasi-compactness of an open of `T` is quasi-compactness of `openOver T V`. -/
instance openOver.instCompactSpace {S : Scheme.{u}} {T : Over S}
    (V : T.left.Opens) [CompactSpace V.toScheme] :
    CompactSpace (openOver T V).left :=
  inferInstanceAs (CompactSpace V.toScheme)

/-- The morphism of test schemes over `S` induced by an inclusion of Zariski opens. -/
def openOverιLE {S : Scheme.{u}} (T : Over S) {V W : T.left.Opens} (hle : V ≤ W) :
    openOver T V ⟶ openOver T W :=
  Over.homMk (T.left.homOfLE hle) (by
    change T.left.homOfLE hle ≫ (W.ι ≫ T.hom) = V.ι ≫ T.hom
    rw [← Category.assoc, Scheme.homOfLE_ι])

/-- `openOverιLE` is `T.left.homOfLE` as a morphism over `S`. -/
theorem openOverιLE_left {S : Scheme.{u}} (T : Over S) {V W : T.left.Opens}
    (hle : V ≤ W) :
    (openOverιLE T hle).left = T.left.homOfLE hle :=
  rfl

/-- The fiber of a relative projective functor over a point of the base functor. -/
abbrev ProjFunctor.pointOver {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜} (F : ProjFunctor X 𝒜) (T : (Over S)ᵒᵖ)
    (t : X.functorOfPoints.obj T) : Type u :=
  { x : F.toFunctor.obj T // F.baseMap.app T x = t }

/-- A functor value canonically decomposes into its base point and the fiber over that
point. -/
def ProjFunctor.objIso {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜} (F : ProjFunctor X 𝒜) (T : (Over S)ᵒᵖ) :
    F.toFunctor.obj T ≃ Σ t : X.functorOfPoints.obj T, F.pointOver T t :=
  (Equiv.sigmaFiberEquiv (F.baseMap.app T)).symm

/-- Reconstructing a functor point from a base point recovers that base point. -/
theorem ProjFunctor.objIso_inv_base {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜} (F : ProjFunctor X 𝒜) (T : (Over S)ᵒᵖ)
    (x : Σ t : X.functorOfPoints.obj T, F.pointOver T t) :
    F.baseMap.app T ((F.objIso T).symm x) = x.1 :=
  x.2.property

/-- A compatible system of values of `F` on quasi-compact opens of a test scheme. -/
structure ProjFunctor.QcCompatibleSystem {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜} (F : ProjFunctor X 𝒜) (T : Over S) where
  /-- The value on each quasi-compact open. -/
  restrict :
    ∀ (V : T.left.Opens) [CompactSpace V.toScheme],
      F.toFunctor.obj (op (openOver T V))
  /-- Restriction along inclusions of quasi-compact opens. -/
  compatible :
    ∀ (V W : T.left.Opens) [CompactSpace V.toScheme] [CompactSpace W.toScheme]
      (hle : V ≤ W),
      F.toFunctor.map (op (openOverιLE T hle)) (restrict W) = restrict V

/-- Construct a compatible system from values on quasi-compact opens that agree
under restriction along inclusions. -/
def ProjFunctor.QcCompatibleSystem.of {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {F : ProjFunctor X 𝒜} {T : Over S}
    (restrict : ∀ (V : T.left.Opens) [CompactSpace V.toScheme],
      F.toFunctor.obj (op (openOver T V)))
    (compatible :
      ∀ (V W : T.left.Opens) [CompactSpace V.toScheme] [CompactSpace W.toScheme]
        (hle : V ≤ W),
        F.toFunctor.map (op (openOverιLE T hle)) (restrict W) = restrict V) :
    F.QcCompatibleSystem T where
  restrict := restrict
  compatible := compatible

/-- A relative projective functor is associated to quadruples when, on quasi-compact
test schemes, its points are equivalence classes of quadruples and its action is
geometric pullback. On a general test scheme a value is the unique compatible system of
those classes on quasi-compact opens, with restriction along `openOverι`. -/
structure ProjFunctor.IsAssociatedToQuadruples {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜} (F : ProjFunctor X 𝒜) (deg : DegreePieces 𝒜) where
  /-- The classifying map sending a quadruple to its functor point, on quasi-compact
  test schemes. -/
  pointOf :
    ∀ (T : Over S) [CompactSpace T.left],
      Quadruple 𝒜 deg T → F.toFunctor.obj (op T)
  /-- A chosen representative quadruple of a functor point, on quasi-compact test
  schemes. -/
  quadrupleOf :
    ∀ (T : Over S) [CompactSpace T.left],
      F.toFunctor.obj (op T) → Quadruple 𝒜 deg T
  /-- The relation between a functor point and a representative quadruple, on
  quasi-compact test schemes. -/
  associated :
    ∀ (T : Over S) [CompactSpace T.left],
      F.toFunctor.obj (op T) → Quadruple 𝒜 deg T → Prop
  /-- `pointOf` classifies its input quadruple. -/
  associated_pointOf :
    ∀ (T : Over S) [CompactSpace T.left] (q : Quadruple 𝒜 deg T),
      associated T (pointOf T q) q
  /-- `quadrupleOf` represents its input functor point. -/
  associated_quadrupleOf :
    ∀ (T : Over S) [CompactSpace T.left] (x : F.toFunctor.obj (op T)),
      associated T x (quadrupleOf T x)
  /-- The structure morphism of a representative is its image in the base functor. -/
  base_eq :
    ∀ (T : Over S) [CompactSpace T.left] (x : F.toFunctor.obj (op T))
      (q : Quadruple 𝒜 deg T),
      associated T x q → q.morphism.app (op T) (𝟙 T) = F.baseMap.app (op T) x
  /-- Equality of points is exactly equivalence of representatives. -/
  eq_iff :
    ∀ (T : Over S) [CompactSpace T.left] (x x' : F.toFunctor.obj (op T))
      (q q' : Quadruple 𝒜 deg T),
      associated T x q → associated T x' q' →
        (x = x' ↔ Quadruple.Equivalent q q')
  /-- The functor action on quasi-compact test schemes is represented by the
  canonical pullback of quadruples. -/
  associated_pullback :
    ∀ (T T' : Over S) [CompactSpace T.left] [CompactSpace T'.left]
      (g : T' ⟶ T) (x : F.toFunctor.obj (op T)) (q : Quadruple 𝒜 deg T),
      associated T x q →
        associated T' (F.toFunctor.map (op g) x) (Quadruple.pullback g q)
  /-- A general value of `F` is a compatible system of quasi-compact values. -/
  qcLimit :
    ∀ T : Over S, F.toFunctor.obj (op T) ≃ F.QcCompatibleSystem T
  /-- The compatible system of a general value is restriction along `openOverι`. -/
  qcLimit_restrict :
    ∀ (T : Over S) (x : F.toFunctor.obj (op T)) (V : T.left.Opens)
      [CompactSpace V.toScheme],
      (qcLimit T x).restrict V = F.toFunctor.map (op (openOverι T V)) x

/-- Construct an association of a relative projective functor with quadruples from the
quasi-compact classifying maps, pullback compatibility, and the quasi-compact open
limit. -/
def ProjFunctor.IsAssociatedToQuadruples.of {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜} {F : ProjFunctor X 𝒜} {deg : DegreePieces 𝒜}
    (pointOf :
      ∀ (T : Over S) [CompactSpace T.left],
        Quadruple 𝒜 deg T → F.toFunctor.obj (op T))
    (quadrupleOf :
      ∀ (T : Over S) [CompactSpace T.left],
        F.toFunctor.obj (op T) → Quadruple 𝒜 deg T)
    (associated :
      ∀ (T : Over S) [CompactSpace T.left],
        F.toFunctor.obj (op T) → Quadruple 𝒜 deg T → Prop)
    (associated_pointOf :
      ∀ (T : Over S) [CompactSpace T.left] (q : Quadruple 𝒜 deg T),
        associated T (pointOf T q) q)
    (associated_quadrupleOf :
      ∀ (T : Over S) [CompactSpace T.left] (x : F.toFunctor.obj (op T)),
        associated T x (quadrupleOf T x))
    (base_eq :
      ∀ (T : Over S) [CompactSpace T.left] (x : F.toFunctor.obj (op T))
        (q : Quadruple 𝒜 deg T),
        associated T x q → q.morphism.app (op T) (𝟙 T) = F.baseMap.app (op T) x)
    (eq_iff :
      ∀ (T : Over S) [CompactSpace T.left] (x x' : F.toFunctor.obj (op T))
        (q q' : Quadruple 𝒜 deg T),
        associated T x q → associated T x' q' →
          (x = x' ↔ Quadruple.Equivalent q q'))
    (associated_pullback :
      ∀ (T T' : Over S) [CompactSpace T.left] [CompactSpace T'.left]
        (g : T' ⟶ T) (x : F.toFunctor.obj (op T)) (q : Quadruple 𝒜 deg T),
        associated T x q →
          associated T' (F.toFunctor.map (op g) x) (Quadruple.pullback g q))
    (qcLimit :
      ∀ T : Over S, F.toFunctor.obj (op T) ≃ F.QcCompatibleSystem T)
    (qcLimit_restrict :
      ∀ (T : Over S) (x : F.toFunctor.obj (op T)) (V : T.left.Opens)
        [CompactSpace V.toScheme],
        (qcLimit T x).restrict V = F.toFunctor.map (op (openOverι T V)) x) :
    F.IsAssociatedToQuadruples deg where
  pointOf := pointOf
  quadrupleOf := quadrupleOf
  associated := associated
  associated_pointOf := associated_pointOf
  associated_quadrupleOf := associated_quadrupleOf
  base_eq := base_eq
  eq_iff := eq_iff
  associated_pullback := associated_pullback
  qcLimit := qcLimit
  qcLimit_restrict := qcLimit_restrict

/-- The classifying maps, association, pullback conditions, and quasi-compact open
limit hold simultaneously. -/
theorem ProjFunctor.IsAssociatedToQuadruples.conditions_spec {S : Scheme.{u}}
    {X : AlgebraicSpace S} {𝒜} {F : ProjFunctor X 𝒜} {deg : DegreePieces 𝒜}
    (h : F.IsAssociatedToQuadruples deg) :
    (∀ (T : Over S) [CompactSpace T.left] (q : Quadruple 𝒜 deg T),
      h.associated T (h.pointOf T q) q) ∧
    (∀ (T : Over S) [CompactSpace T.left] (x : F.toFunctor.obj (op T)),
      h.associated T x (h.quadrupleOf T x)) ∧
    (∀ (T : Over S) [CompactSpace T.left] (x : F.toFunctor.obj (op T))
        (q : Quadruple 𝒜 deg T),
      h.associated T x q →
        q.morphism.app (op T) (𝟙 T) = F.baseMap.app (op T) x) ∧
    (∀ (T : Over S) [CompactSpace T.left] (x x' : F.toFunctor.obj (op T))
        (q q' : Quadruple 𝒜 deg T),
      h.associated T x q → h.associated T x' q' →
        (x = x' ↔ Quadruple.Equivalent q q')) ∧
    (∀ (T T' : Over S) [CompactSpace T.left] [CompactSpace T'.left]
        (g : T' ⟶ T) (x : F.toFunctor.obj (op T)) (q : Quadruple 𝒜 deg T),
      h.associated T x q →
        h.associated T' (F.toFunctor.map (op g) x) (Quadruple.pullback g q)) ∧
    (∀ (T : Over S) (x : F.toFunctor.obj (op T)) (V : T.left.Opens)
        [CompactSpace V.toScheme],
      (h.qcLimit T x).restrict V = F.toFunctor.map (op (openOverι T V)) x) :=
  ⟨h.associated_pointOf, h.associated_quadrupleOf, h.base_eq, h.eq_iff,
    h.associated_pullback, h.qcLimit_restrict⟩

/-- Every functor point of a quasi-compact test scheme has a representative quadruple. -/
theorem ProjFunctor.IsAssociatedToQuadruples.exists_quadruple {S : Scheme.{u}}
    {X : AlgebraicSpace S} {𝒜} {F : ProjFunctor X 𝒜} {deg : DegreePieces 𝒜}
    (h : F.IsAssociatedToQuadruples deg) (T : Over S) [CompactSpace T.left]
    (x : F.toFunctor.obj (op T)) :
    ∃ q : Quadruple 𝒜 deg T, h.associated T x q :=
  ⟨h.quadrupleOf T x, h.associated_quadrupleOf T x⟩

/-- Every quadruple over a quasi-compact test scheme represents a functor point. -/
theorem ProjFunctor.IsAssociatedToQuadruples.exists_point {S : Scheme.{u}}
    {X : AlgebraicSpace S} {𝒜} {F : ProjFunctor X 𝒜} {deg : DegreePieces 𝒜}
    (h : F.IsAssociatedToQuadruples deg) (T : Over S) [CompactSpace T.left]
    (q : Quadruple 𝒜 deg T) :
    ∃ x : F.toFunctor.obj (op T), h.associated T x q :=
  ⟨h.pointOf T q, h.associated_pointOf T q⟩

/-- Restriction of a general functor value to a quasi-compact open is associated to a
quadruple. -/
theorem ProjFunctor.IsAssociatedToQuadruples.restrict_exists_quadruple
    {S : Scheme.{u}} {X : AlgebraicSpace S} {𝒜}
    {F : ProjFunctor X 𝒜} {deg : DegreePieces 𝒜}
    (h : F.IsAssociatedToQuadruples deg) (T : Over S)
    (x : F.toFunctor.obj (op T)) (V : T.left.Opens)
    [CompactSpace V.toScheme] :
    ∃ q : Quadruple 𝒜 deg (openOver T V),
      h.associated (openOver T V) (F.toFunctor.map (op (openOverι T V)) x) q :=
  h.exists_quadruple (openOver T V) (F.toFunctor.map (op (openOverι T V)) x)

/-- The compatible system attached to a general functor value by `qcLimit`. -/
def ProjFunctor.QcCompatibleSystem.ofPoint {S : Scheme.{u}}
    {X : AlgebraicSpace S} {𝒜} {F : ProjFunctor X 𝒜} {deg : DegreePieces 𝒜}
    (h : F.IsAssociatedToQuadruples deg) (T : Over S)
    (x : F.toFunctor.obj (op T)) :
    F.QcCompatibleSystem T :=
  h.qcLimit T x

/-- Restriction of a general value along `openOverι` is the stored compatible system. -/
theorem ProjFunctor.QcCompatibleSystem.ofPoint_restrict
    {S : Scheme.{u}} {X : AlgebraicSpace S} {𝒜}
    {F : ProjFunctor X 𝒜} {deg : DegreePieces 𝒜}
    (h : F.IsAssociatedToQuadruples deg) (T : Over S)
    (x : F.toFunctor.obj (op T)) (V : T.left.Opens)
    [CompactSpace V.toScheme] :
    (ProjFunctor.QcCompatibleSystem.ofPoint h T x).restrict V = F.toFunctor.map (op (openOverι T V)) x :=
  h.qcLimit_restrict T x V

/-- The compatible system of a functor point is its restriction to quasi-compact opens,
and these restrictions agree along inclusions. -/
theorem ProjFunctor.QcCompatibleSystem.conditions_spec
    {S : Scheme.{u}} {X : AlgebraicSpace S} {𝒜}
    {F : ProjFunctor X 𝒜} {deg : DegreePieces 𝒜}
    (h : F.IsAssociatedToQuadruples deg) (T : Over S)
    (x : F.toFunctor.obj (op T)) :
    (∀ (V : T.left.Opens) [CompactSpace V.toScheme],
      (ProjFunctor.QcCompatibleSystem.ofPoint h T x).restrict V =
        F.toFunctor.map (op (openOverι T V)) x) ∧
    (∀ (V W : T.left.Opens) [CompactSpace V.toScheme] [CompactSpace W.toScheme]
        (hle : V ≤ W),
      F.toFunctor.map (op (openOverιLE T hle))
          ((ProjFunctor.QcCompatibleSystem.ofPoint h T x).restrict W) =
        (ProjFunctor.QcCompatibleSystem.ofPoint h T x).restrict V) :=
  ⟨ProjFunctor.QcCompatibleSystem.ofPoint_restrict h T x, (h.qcLimit T x).compatible⟩

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
