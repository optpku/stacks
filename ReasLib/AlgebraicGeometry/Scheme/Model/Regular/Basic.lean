module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

/-- A regular proper model of a smooth projective curve over the fraction field of a
discrete valuation ring, together with its identification on the generic fibre. -/
structure RegularModel.{u} (R K : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom] where
  /-- The scheme underlying the model. -/
  scheme : Scheme.{u}
  /-- The structural morphism of the model over the discrete valuation ring. -/
  base : scheme ⟶ Spec (CommRingCat.of R)
  /-- The model scheme is Noetherian. -/
  isNoetherian : IsNoetherian scheme
  /-- The structural morphism is flat. -/
  flat : Flat base
  /-- The structural morphism is of finite type. -/
  finiteType : FiniteType base
  /-- The structural morphism is proper. -/
  proper : IsProper base
  /-- The model scheme is regular. -/
  regular : Scheme.Regular scheme
  /-- The generic fibre is identified with the given curve. -/
  genericFiberIso : C ≅ Over.mk
    (pullback.snd base (Spec.map (CommRingCat.ofHom (algebraMap R K))))

universe u

namespace RegularModel

/-- Construct a regular model from its structural data and generic-fibre identification. -/
def ofData {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (h_noetherian : IsNoetherian X) (h_flat : Flat f) (h_finiteType : FiniteType f)
    (h_proper : IsProper f) (h_regular : Scheme.Regular X)
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))) :
    RegularModel R K C :=
  { scheme := X
    base := f
    isNoetherian := h_noetherian
    flat := h_flat
    finiteType := h_finiteType
    proper := h_proper
    regular := h_regular
    genericFiberIso := genericFiberIso }

/-- A regular proper model has Noetherian regular source and flat, finite-type, proper
structural morphism. -/
theorem spec {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    (M : RegularModel R K C) :
    IsNoetherian M.scheme ∧ Flat M.base ∧ FiniteType M.base ∧ IsProper M.base ∧
      Scheme.Regular M.scheme :=
  ⟨M.isNoetherian, M.flat, M.finiteType, M.proper, M.regular⟩

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]

/-- Two regular models are isomorphic when an isomorphism over the discrete valuation ring
intertwines their chosen identifications of the generic fibre with the curve. -/
def Isomorphic (M N : RegularModel R K C) : Prop :=
  ∃ e : Over.mk M.base ≅ Over.mk N.base,
    M.genericFiberIso.hom ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map e.hom =
      N.genericFiberIso.hom

/-- A marked isomorphism of regular models is exactly a slice isomorphism whose pullback
intertwines the chosen generic-fibre identifications. -/
theorem isomorphic_iff (M N : RegularModel R K C) :
    Isomorphic M N ↔
      ∃ e : Over.mk M.base ≅ Over.mk N.base,
        M.genericFiberIso.hom ≫
            (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map e.hom =
          N.genericFiberIso.hom := Iff.rfl

end RegularModel

end AlgebraicGeometry.Scheme.Hom
