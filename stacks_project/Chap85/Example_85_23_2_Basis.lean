module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.SetTheory.Cardinal.ENat
public import Mathlib.Topology.KrullDimension
public import ReasLib.CategoryTheory.Sites.EnoughObjects
public import stacks_project.Chap85.Example_85_23_2_Site

/-!
# Quasi-compact basis, Gabber bound, and étale covering systems

The quasi-compact objects of the locally finite type étale slice, the explicit cohomological
bound `d_V`, and the étale coverings with quasi-compact members.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Quasi-compact objects of the locally finite type étale slice of `S`. -/
def quasiCompact (S : Scheme.{u}) : ObjectProperty (locallyOfFiniteTypeOver S) :=
  fun V ↦ CompactSpace V.left

/-- An object lies in the quasi-compact basis iff its underlying scheme is compact. -/
theorem mem_quasiCompact_iff {S : Scheme.{u}} {V : locallyOfFiniteTypeOver S} :
    quasiCompact S V ↔ CompactSpace V.left :=
  sorry

/-- Transcendence degree of `κ(v)` over `κ(s)`, where `s` is the image of `v` in `S`. -/
def residueExtensionTrdeg {S : Scheme.{u}} (V : locallyOfFiniteTypeOver S) (v : V.left) :
    WithBot ℕ∞ :=
  (@Algebra.trdeg (S.residueField (V.hom v) : Type u) (V.left.residueField v : Type u) _ _
      (RingHom.toAlgebra (V.hom.residueFieldMap v).hom)).toENat

/-- The source cohomological bound formula on a locally finite type `S`-scheme, valued in
`WithBot ℕ∞`. -/
def cohomologyBoundFormula {S : Scheme.{u}} (V : locallyOfFiniteTypeOver S) : WithBot ℕ∞ :=
  1 + 2 * topologicalKrullDim S +
    (⨆ v, residueExtensionTrdeg V v + 2 * ringKrullDim (V.left.presheaf.stalk v))

/-- The integer Gabber bound `d_V`, obtained by truncating `cohomologyBoundFormula` at `⊥` and
`⊤`. -/
def cohomologyBound {S : Scheme.{u}} (V : locallyOfFiniteTypeOver S) : ℤ :=
  ((cohomologyBoundFormula V).unbotD 0).toNat

/-- When the source formula is finite, the integer bound recovers
`1 + 2 dim S + sup_v (trdeg_{κ(s)}(κ(v)) + 2 dim O_{V,v})`. -/
theorem cohomologyBound_spec {S : Scheme.{u}} (V : locallyOfFiniteTypeOver S) {n : ℕ}
    (hn : cohomologyBoundFormula V = n) :
    cohomologyBound V = n :=
  sorry

/-- Étale coverings of `V` with quasi-compact members. -/
def coveringSystem (S : Scheme.{u}) (V : locallyOfFiniteTypeOver S) :
    Set (FormalCoproduct.{u} (Over V)) :=
  {cover | ((etaleTopology S).over V).CoversTop cover.obj ∧
    ∀ i : cover.I,
      Etale (cover.obj i).hom.left ∧ CompactSpace (cover.obj i).left.left}

/-- Membership in the chosen covering system is an étale covering by quasi-compact objects. -/
theorem mem_coveringSystem_iff {S : Scheme.{u}} {V : locallyOfFiniteTypeOver S}
    {cover : FormalCoproduct.{u} (Over V)} :
    cover ∈ coveringSystem S V ↔
      ((etaleTopology S).over V).CoversTop cover.obj ∧
        ∀ i : cover.I,
          Etale (cover.obj i).hom.left ∧ CompactSpace (cover.obj i).left.left :=
  sorry

/-- A selected covering-system family covers `V` in the slice étale topology. -/
theorem coveringSystem_isCover {S : Scheme.{u}} {V : locallyOfFiniteTypeOver S}
    {cover : FormalCoproduct.{u} (Over V)} (hcover : cover ∈ coveringSystem S V) :
    ((etaleTopology S).over V).CoversTop cover.obj :=
  sorry

/-- Quasi-compact étale coverings are cofinal among étale coverings of `V`. -/
theorem coveringSystem_cofinal {S : Scheme.{u}} {V : locallyOfFiniteTypeOver S}
    {ι : Type u} (family : ι → Over V)
    (hfamily : ((etaleTopology S).over V).CoversTop family) :
    ∃ cover : FormalCoproduct.{u} (Over V),
      cover ∈ coveringSystem S V ∧
        Nonempty (cover ⟶ FormalCoproduct.mk ι family) :=
  sorry

/-- Every object of the locally finite type étale slice admits an étale covering by quasi-compact
objects. -/
theorem hasEnoughQuasiCompact (S : Scheme.{u}) :
    (etaleTopology S).HasEnoughObjectsWithProperty (quasiCompact S) :=
  sorry

end AlgebraicGeometry.Scheme.Etale
