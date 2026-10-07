module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.RingTheory.PowerSeries.Basic
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap65.Example_65_14_1_Space
public import stacks_project.Chap67.Lemma_67_48_6_Reduced

/-!
# Formal disk maps into the affine-line involution sheaf

This module records the formal disk `Y = Spec (PowerSeries k)` and the two
maps into the involution quotient sheaf `X` of Spaces, Example 65.14.1,
induced by `x ↦ x` and `x ↦ -x`. Quasi-separatedness of `X` is
`quasiCompact_diag_sheafOfPoints`; failure of local separatedness is
`not_isImmersion_diag_sheafOfPoints`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution

/-- The structure morphism `Spec (PowerSeries k) ⟶ Spec k`. -/
def formalDiskHom (k : Type u) [Field k] :
    Spec (CommRingCat.of (PowerSeries k)) ⟶ base k :=
  Spec.map (CommRingCat.ofHom (PowerSeries.C : k →+* PowerSeries k))

/-- `formalDiskHom k` is `Spec.map` of the constant-series homomorphism. -/
theorem formalDiskHom_eq (k : Type u) [Field k] :
    formalDiskHom k =
      Spec.map (CommRingCat.ofHom (PowerSeries.C : k →+* PowerSeries k)) := sorry

/-- The formal disk `Y = Spec (PowerSeries k)` as a scheme over `Spec k`. -/
def formalDisk (k : Type u) [Field k] : Over (base k) :=
  Over.mk (formalDiskHom k)

/-- The underlying scheme of the formal disk is `Spec (PowerSeries k)`. -/
theorem formalDisk_left (k : Type u) [Field k] :
    (formalDisk k).left = Spec (CommRingCat.of (PowerSeries k)) := sorry

/-- The structure morphism of the formal disk is `formalDiskHom k`. -/
theorem formalDisk_hom (k : Type u) [Field k] :
    (formalDisk k).hom = formalDiskHom k := sorry

/-- The global coordinate section of `Spec (PowerSeries k)`, the image of
`PowerSeries.X`. -/
def formalDiskCoord (k : Type u) [Field k] : Γ((formalDisk k).left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv PowerSeries.X

/-- `formalDiskCoord k` is the image of `PowerSeries.X` under `ΓSpecIso`. -/
theorem formalDiskCoord_eq (k : Type u) [Field k] :
    formalDiskCoord k =
      (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv PowerSeries.X := sorry

/-- The scheme map `Spec (PowerSeries k) ⟶ 𝔸¹_k` induced by the coordinate
`PowerSeries.X` is a morphism over `Spec k`. -/
theorem toCover_w (k : Type u) [Field k] :
    AffineSpace.homOfVector (formalDisk k).hom
        (fun _ : ULift.{u} (Fin 1) ↦ formalDiskCoord k) ≫
      (cover k).hom =
      (formalDisk k).hom := sorry

/-- The morphism `Y ⟶ U` over `Spec k` induced by `x ↦ x`. -/
def toCover (k : Type u) [Field k] : formalDisk k ⟶ cover k :=
  Over.homMk
    (AffineSpace.homOfVector (formalDisk k).hom
      (fun _ : ULift.{u} (Fin 1) ↦ formalDiskCoord k))
    (toCover_w k)

/-- The underlying scheme map of `toCover k` is `homOfVector` of `formalDiskCoord k`. -/
theorem toCover_eq (k : Type u) [Field k] :
    (toCover k).left =
      AffineSpace.homOfVector (formalDisk k).hom
        (fun _ : ULift.{u} (Fin 1) ↦ formalDiskCoord k) := sorry

/-- The morphism `Y ⟶ U` over `Spec k` induced by `x ↦ -x`. -/
def toCoverNeg (k : Type u) [Field k] : formalDisk k ⟶ cover k :=
  toCover k ≫ involution k

/-- `toCoverNeg k` is `toCover k` followed by coordinatewise negation. -/
theorem toCoverNeg_eq (k : Type u) [Field k] :
    toCoverNeg k = toCover k ≫ involution k := sorry

/-- The morphism `a : Y ⟶ X` induced by `x ↦ x` on `𝔸¹_k`, as a morphism of
fppf sheaves into `sheafOfPoints k`. -/
def fromDisk (k : Type u) [Field k] [NeZero (2 : k)] :
    (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj (formalDisk k) ⟶
      sheafOfPoints k :=
  (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (toCover k) ≫ atlas k

/-- `fromDisk k` is the composite of `uliftYoneda.map (toCover k)` with the
existing atlas of `sheafOfPoints k`. -/
theorem fromDisk_eq (k : Type u) [Field k] [NeZero (2 : k)] :
    fromDisk k =
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (toCover k) ≫
        atlas k := sorry

/-- The morphism `b : Y ⟶ X` induced by `x ↦ -x` on `𝔸¹_k`, as a morphism of
fppf sheaves into `sheafOfPoints k`. -/
def fromDiskNeg (k : Type u) [Field k] [NeZero (2 : k)] :
    (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj (formalDisk k) ⟶
      sheafOfPoints k :=
  (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (toCoverNeg k) ≫
    atlas k

/-- `fromDiskNeg k` is the composite of `uliftYoneda.map (toCoverNeg k)` with the
existing atlas of `sheafOfPoints k`. -/
theorem fromDiskNeg_eq (k : Type u) [Field k] [NeZero (2 : k)] :
    fromDiskNeg k =
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (toCoverNeg k) ≫
        atlas k := sorry

/-- The scheme endomorphism of `Spec (PowerSeries k)` sending a series `f(X)` to
`f(-X)`. -/
def formalDiskNegHom (k : Type u) [Field k] :
    (formalDisk k).left ⟶ (formalDisk k).left :=
  Spec.map (CommRingCat.ofHom (PowerSeries.evalNegHom : PowerSeries k →+* PowerSeries k))

/-- `formalDiskNegHom k` is `Spec.map` of `PowerSeries.evalNegHom`. -/
theorem formalDiskNegHom_eq (k : Type u) [Field k] :
    formalDiskNegHom k =
      Spec.map (CommRingCat.ofHom
        (PowerSeries.evalNegHom : PowerSeries k →+* PowerSeries k)) := sorry

/-- Negation of the formal coordinate commutes with the structure morphism to
`Spec k`. -/
theorem formalDiskNeg_w (k : Type u) [Field k] :
    formalDiskNegHom k ≫ (formalDisk k).hom = (formalDisk k).hom := sorry

/-- The automorphism `-1` of the formal disk over `Spec k`. -/
def formalDiskNeg (k : Type u) [Field k] : formalDisk k ⟶ formalDisk k :=
  Over.homMk (formalDiskNegHom k) (formalDiskNeg_w k)

/-- The underlying scheme map of `formalDiskNeg k` is `formalDiskNegHom k`. -/
theorem formalDiskNeg_left (k : Type u) [Field k] :
    (formalDiskNeg k).left = formalDiskNegHom k := sorry

/-- Composing `a` with `-1` recovers `b`. -/
theorem formalDiskNeg_comp (k : Type u) [Field k] [NeZero (2 : k)] :
    (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (formalDiskNeg k) ≫
      fromDisk k =
      fromDiskNeg k := sorry

/-- The involution quotient sheaf is reduced: its atlas source `𝔸¹_k` is reduced. -/
theorem isReduced_sheafOfPoints (k : Type u) [Field k] [NeZero (2 : k)] :
    AlgebraicGeometry.IsReduced (cover k).left := sorry

/-- The formal disk, as an algebraic space, is reduced. -/
instance instIsReduced_formalDisk (k : Type u) [Field k] :
    IsReduced (ofOver (formalDisk k)) := sorry

/-- The formal disk, as an algebraic space, is quasi-separated. -/
instance instIsQuasiSeparated_formalDisk (k : Type u) [Field k] :
    IsQuasiSeparated (ofOver (formalDisk k)) := sorry

end AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution
