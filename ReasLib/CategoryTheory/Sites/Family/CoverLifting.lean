/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Grothendieck
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.SetTheory.Cardinal.Order
public import ReasLib.CategoryTheory.Sites.Family.Covering

/-!
# Finite-cover lifting for maps of covariant set-valued functors

The predicate in this file records that the image of a section under a natural
transformation can be lifted through one member of every finite covering
family.  It is formulated using the fixed-target family owner
`SemiRepresentableFamily.Over`.
-/

@[expose] public section

open CategoryTheory

universe q u v w w'

namespace CategoryTheory.NatTrans

variable {C : Type u} [Category.{v} C]
variable {p q : C ⥤ Type w} {J : GrothendieckTopology C}

/-- `η` lifts `x` through the fixed-target family `𝒰` when its image is the restriction of a
section in one member of that family.  The covering-family index may live in a universe
independent of the values of `p` and `q`. -/
def CoverLift (η : p ⟶ q) {W : C}
    (𝒰 : SemiRepresentableFamily.Over.{w'} W) (x : p.obj W) : Prop :=
  ∃ i : 𝒰.index, ∃ y : q.obj (𝒰.obj i).left,
    q.map (𝒰.obj i).hom y = η.app W x

/-- `η` has finite-cover lifts for `J` when every element in its image locally comes from a
member of each finite covering family. -/
def FiniteCoverLifts (η : p ⟶ q) (J : GrothendieckTopology C) : Prop :=
  ∀ {W : C} (𝒰 : SemiRepresentableFamily.Over.{w'} W) [Finite 𝒰.index]
    (_ : 𝒰.toSieve ∈ J W) (x : p.obj W), η.CoverLift 𝒰 x

namespace CoverLift

variable {η : p ⟶ q}

/-- Unpack a cover-lifting witness into its covering-family index and local section. -/
theorem exists_data {W : C} {𝒰 : SemiRepresentableFamily.Over.{w'} W} {x : p.obj W}
    (hη : η.CoverLift 𝒰 x) :
    ∃ i : 𝒰.index, ∃ y : q.obj (𝒰.obj i).left,
      q.map (𝒰.obj i).hom y = η.app W x := sorry

end CoverLift

namespace FiniteCoverLifts

variable {η : p ⟶ q}

/-- Apply a finite-cover lifting witness to one covering family and one source element. -/
theorem exists_lift (hη : η.FiniteCoverLifts J)
    {W : C} (𝒰 : SemiRepresentableFamily.Over.{w'} W) [Finite 𝒰.index]
    (h𝒰 : 𝒰.toSieve ∈ J W) (x : p.obj W) :
    η.CoverLift 𝒰 x := sorry

end FiniteCoverLifts

end CategoryTheory.NatTrans

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C]
variable {p : C ⥤ Type w} {J : GrothendieckTopology C}

/-- `p` has finite-cover lifts for `J` when every element of `p` locally lifts through one member
of each finite covering family. Unlike `NatTrans.FiniteCoverLifts`, this is a property of the
target functor itself, so it is suitable for constructing a point from that functor. -/
def FiniteCoverLifts (p : C ⥤ Type w) (J : GrothendieckTopology C) : Prop :=
  ∀ {W : C} (𝒰 : SemiRepresentableFamily.Over.{w'} W) [Finite 𝒰.index]
    (_ : 𝒰.toSieve ∈ J W) (x : p.obj W),
      ∃ i : 𝒰.index, ∃ y : p.obj (𝒰.obj i).left,
        p.map (𝒰.obj i).hom y = x

namespace FiniteCoverLifts

/-- Apply a finite-cover lifting property to one finite covering family and one element. -/
theorem exists_lift (hp : p.FiniteCoverLifts J)
    {W : C} (𝒰 : SemiRepresentableFamily.Over.{w'} W) [Finite 𝒰.index]
    (h𝒰 : 𝒰.toSieve ∈ J W) (x : p.obj W) :
    ∃ i : 𝒰.index, ∃ y : p.obj (𝒰.obj i).left,
      p.map (𝒰.obj i).hom y = x := sorry

end FiniteCoverLifts

/- Namespace for concrete finite-cover lifting obligations. -/
namespace CoverLift

/-- A concrete finite-cover lifting obligation for a covariant set-valued
functor. The cover is stored with canonical `Fin n` indexing so the request
can be scheduled without retaining an arbitrary finite index universe. -/
@[stacks 00YP "finite-cover lifting request"]
structure Request (J : GrothendieckTopology C) (p : C ⥤ Type w) where
  /-- The object at which the local lifting is requested. -/
  W : C
  /-- The cardinality of the stored finite cover. -/
  n : ℕ
  /-- The arrows in the canonically finite-indexed cover. -/
  obj : Fin n → CategoryTheory.Over W
  /-- The stored finite family generates a `J`-covering sieve. -/
  h𝒰 : (SemiRepresentableFamily.Over.toSieve
    ({ index := Fin n, obj := obj } : SemiRepresentableFamily.Over.{0} W)) ∈ J W
  /-- The section to be lifted locally. -/
  f : p.obj W

namespace Request

/-- The finite covering family carried by a finite-cover lifting request. -/
abbrev cover (r : Request J p) : SemiRepresentableFamily.Over.{0} r.W where
  index := Fin r.n
  obj := r.obj

/-- Form the canonical finite-indexed request represented by an arbitrary finite covering
family.  The source family is reindexed through `finReindex`, so the request stores concrete
finite data without retaining the family's original index universe. -/
noncomputable def ofFamily {W : C}
    (𝒰 : SemiRepresentableFamily.Over.{w'} W) [Finite 𝒰.index]
    (h𝒰 : 𝒰.toSieve ∈ J W) (f : p.obj W) : Request J p where
  W := W
  n := Nat.card 𝒰.index
  obj := (SemiRepresentableFamily.Over.finReindex 𝒰).obj
  h𝒰 := Eq.mpr
    (congrArg (fun R => R ∈ J W) (SemiRepresentableFamily.Over.finReindex_toSieve 𝒰)) h𝒰
  f := f

/-- The cover stored by `ofFamily` is the canonical finite reindexing of its input family. -/
@[simp]
theorem ofFamily_cover {W : C}
    (𝒰 : SemiRepresentableFamily.Over.{w'} W) [Finite 𝒰.index]
    (h𝒰 : 𝒰.toSieve ∈ J W) (f : p.obj W) :
    (ofFamily 𝒰 h𝒰 f).cover = SemiRepresentableFamily.Over.finReindex 𝒰 := rfl

/-- A finite-cover lifting request is realized when its stored section lifts
through one arrow of its stored cover. -/
def is_realized (r : Request J p) : Prop :=
  ∃ i : r.cover.index, ∃ y : p.obj (r.cover.obj i).left,
    p.map (r.cover.obj i).hom y = r.f

/-- Realization of the canonical request for a finite family is exactly local lifting through
the original family. -/
theorem ofFamily_is_realized_iff {W : C}
    (𝒰 : SemiRepresentableFamily.Over.{w'} W) [Finite 𝒰.index]
    (h𝒰 : 𝒰.toSieve ∈ J W) (f : p.obj W) :
    (ofFamily 𝒰 h𝒰 f).is_realized ↔
      ∃ i : 𝒰.index, ∃ y : p.obj (𝒰.obj i).left,
        p.map (𝒰.obj i).hom y = f := sorry

/-- Transport a finite-cover lifting request along a natural transformation. -/
def map (r : Request J p) {q : C ⥤ Type w} (η : p ⟶ q) :
    Request J q where
  W := r.W
  n := r.n
  obj := r.obj
  h𝒰 := r.h𝒰
  f := η.app r.W r.f

/-- Transporting a finite-cover lifting request along the identity natural
transformation leaves the request unchanged. -/
@[simp]
theorem map_id (r : Request J p) :
    r.map (𝟙 p) = r := sorry

/-- Transporting a finite-cover lifting request through two natural
transformations agrees with transport through their composite. -/
@[simp]
theorem map_comp {q s : C ⥤ Type w} (r : Request J p)
    (η : p ⟶ q) (θ : q ⟶ s) :
    (r.map η).map θ = r.map (η ≫ θ) := sorry

/-- Transport of a finite-cover lifting request respects equality of natural
transformations. -/
theorem map_congr {q : C ⥤ Type w} (r : Request J p)
    {η η' : p ⟶ q} (hη : η = η') :
    r.map η = r.map η' := sorry

/-- `r` is solved by `η` when the transported request is realized in the
target functor.  This packages the recurring refinement-stage condition
without committing to a particular presentation of the source or target
inverse system. -/
def is_solved_by (r : Request J p) {q : C ⥤ Type w} (η : p ⟶ q) : Prop :=
  (r.map η).is_realized

/-- A cover-lifting witness for a natural transformation is exactly realization
of the transported finite-cover request. -/
theorem is_realized_map_iff_cover_lift {q : C ⥤ Type w}
    (r : Request J p) (η : p ⟶ q) :
    (r.map η).is_realized ↔ η.CoverLift r.cover r.f := sorry

/-- A request is solved by a natural transformation exactly when the image of
its stored section admits a lift through its stored finite cover. -/
@[simp]
theorem is_solved_by_iff_cover_lift {q : C ⥤ Type w}
    (r : Request J p) (η : p ⟶ q) :
    r.is_solved_by η ↔ η.CoverLift r.cover r.f := sorry

/-- Realization of a finite-cover lifting request persists after transport
along a natural transformation. -/
theorem is_realized_map (r : Request J p) {q : C ⥤ Type w}
    (η : p ⟶ q) :
    r.is_realized → (r.map η).is_realized := sorry

/-- A request solved after one natural transformation remains solved after
postcomposition. -/
theorem is_solved_by_comp {q s : C ⥤ Type w} (r : Request J p)
    (η : p ⟶ q) (θ : q ⟶ s) :
    r.is_solved_by η → r.is_solved_by (η ≫ θ) := sorry

/-- A request already realized in its source functor is solved by every
natural transformation out of that functor. -/
theorem is_solved_by_of_is_realized (r : Request J p) {q : C ⥤ Type w}
    (η : p ⟶ q) : r.is_realized → r.is_solved_by η := sorry

/-- Realization of every canonical finite-cover request is equivalent to finite-cover lifting
of the underlying functor. -/
theorem all_realized_iff (p : C ⥤ Type w) :
    (∀ r : Request J p, r.is_realized) ↔ Functor.FiniteCoverLifts.{u, v, w, w'} p J := sorry

/-- Solving every canonical source request by a natural transformation is equivalent to its
finite-cover lifting property. -/
theorem all_solved_by_iff {q : C ⥤ Type w} (η : p ⟶ q) :
    (∀ r : Request J p, r.is_solved_by η) ↔ NatTrans.FiniteCoverLifts.{u, v, w, w'} η J := sorry

end Request

/-! The scheduling layer only uses the concrete request type.  It deliberately lives beside that
type rather than in a Chapter-specific transfinite-recursion module. -/
namespace Request

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C} {p : C ⥤ Type w}

/-- Finite-cover requests for `p` are small in the universe generated by the site, its homs, and
the values of `p`. -/
theorem small (p : C ⥤ Type w) : Small.{max u v w} (Request J p) := sorry

/-- Transfer the canonical smallness of finite-cover requests to any larger target universe. -/
theorem small_of_univLE (p : C ⥤ Type w) [UnivLE.{max u v w, q}] :
    Small.{q} (Request J p) := sorry

/-! A schedule is a canonical small code type for requests. Its universe is an explicit part of
the API, so a downstream transfinite construction may choose its own indexing universe. -/
namespace Schedule

variable {q}

/-- A canonical request-code type in any universe in which the concrete request type is small. -/
abbrev model (p : C ⥤ Type w) [UnivLE.{max u v w, q}] : Type q :=
  Shrink.{q} (Request J p)

/-- Decode a canonical request code to the corresponding concrete request. -/
noncomputable def decode (p : C ⥤ Type w) [UnivLE.{max u v w, q}] :
    model (J := J) p → Request J p :=
  (equivShrink (Request J p)).symm

/-- Every finite-cover request has a canonical small code. -/
theorem decode_surjective (p : C ⥤ Type w) [UnivLE.{max u v w, q}] :
    Function.Surjective (decode (J := J) p) := sorry

/-- A chosen well-order of the request codes. -/
noncomputable def well_order (p : C ⥤ Type w) [UnivLE.{max u v w, q}] :
    model (J := J) p → model (J := J) p → Prop :=
  WellOrderingRel

/-- The canonical request-code ordering is a well-order. -/
instance well_order_is_well_order (p : C ⥤ Type w) [UnivLE.{max u v w, q}] :
    IsWellOrder (model (J := J) p) (well_order (J := J) p) := sorry

/-- The linear order underlying the canonical request-code well-order. -/
@[reducible] noncomputable def linear_order (p : C ⥤ Type w) [UnivLE.{max u v w, q}] :
    LinearOrder (model (J := J) p) :=
  IsWellOrder.linearOrder (well_order (J := J) p)

/-- The canonical order on request codes is available to downstream constructions through
typeclass inference.  It is the order returned by `linear_order`, so callers do not need to pin a
repeated local `letI` when using the schedule as a transfinite index. -/
noncomputable instance instLinearOrder (p : C ⥤ Type w) [UnivLE.{max u v w, q}] :
    LinearOrder (model (J := J) p) :=
  linear_order (J := J) p

/-- The canonical request-code well-order is well-founded. -/
theorem well_founded (p : C ⥤ Type w) [UnivLE.{max u v w, q}] :
    WellFounded (well_order (J := J) p) := sorry

/-- The strict order induced by the canonical schedule order is well-founded. -/
noncomputable instance instWellFoundedLt (p : C ⥤ Type w) [UnivLE.{max u v w, q}] :
    WellFoundedLT (model (J := J) p) :=
  (well_order_is_well_order (J := J) p).toIsWellFounded

/-- The `WithTop` completion of a request schedule has the canonical bottom induced by its
well-founded order. -/
noncomputable instance instTopOrderBot (p : C ⥤ Type w) [UnivLE.{max u v w, q}] :
    OrderBot (WithTop (model (J := J) p)) :=
  WellFoundedLT.toOrderBot (WithTop (model (J := J) p))

/-- The `WithTop` completion of a request schedule carries the canonical successor operation used
by well-founded transfinite recursion. -/
noncomputable instance instTopSuccOrder (p : C ⥤ Type w) [UnivLE.{max u v w, q}] :
    SuccOrder (WithTop (model (J := J) p)) :=
  SuccOrder.ofLinearWellFoundedLT (WithTop (model (J := J) p))

end Schedule
end Request
end CoverLift

end CategoryTheory.Functor

namespace CategoryTheory.NatTrans.FiniteCoverLifts

variable {C : Type u} [Category.{v} C]
variable {p q : C ⥤ Type w} {J : GrothendieckTopology C}

/-- Finite-cover lifting of a target functor induces finite-cover lifting along every map into
that target. -/
theorem of_target (η : p ⟶ q) (hq : Functor.FiniteCoverLifts.{u, v, w, w'} q J) :
    NatTrans.FiniteCoverLifts.{u, v, w, w'} η J := sorry

end CategoryTheory.NatTrans.FiniteCoverLifts
