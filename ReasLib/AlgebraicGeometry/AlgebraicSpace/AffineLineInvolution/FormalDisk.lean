module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reduced
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation

/-!
# Formal disk maps into the affine-line involution quotient

The coordinate and its negative define unequal maps from the formal disk into the
punctured-negation quotient of the affine line, although they agree on all field-valued
points. The identity and negation pre-relation on the disk therefore gives a
set-theoretically invariant map that is not invariant.
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

/-- The map from the formal disk to the affine line over `Spec k` induced by its coordinate. -/
def toCover (k : Type u) [Field k] : formalDisk k ⟶ cover k :=
  Over.homMk
    (AffineSpace.homOfVector (formalDisk k).hom
      (fun _ : ULift.{u} (Fin 1) ↦ formalDiskCoord k))
    (AffineSpace.homOfVector_over (formalDisk k).hom
      (fun _ : ULift.{u} (Fin 1) ↦ formalDiskCoord k))

/-- The underlying scheme map of `toCover k` is `homOfVector` of `formalDiskCoord k`. -/
theorem toCover_eq (k : Type u) [Field k] :
    (toCover k).left =
      AffineSpace.homOfVector (formalDisk k).hom
        (fun _ : ULift.{u} (Fin 1) ↦ formalDiskCoord k) := sorry

/-- The map from the formal disk to the affine line over `Spec k` induced by the negative
formal coordinate. -/
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

/-- Negation on the formal disk followed by its coordinate-induced map to the quotient
equals the map induced by the negative coordinate. -/
theorem formalDiskNeg_comp (k : Type u) [Field k] [NeZero (2 : k)] :
    (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (formalDiskNeg k) ≫
      fromDisk k =
      fromDiskNeg k := sorry

/-- The involution quotient sheaf admits a representable étale locally-surjective atlas
from a reduced scheme. -/
theorem isReduced_sheafOfPoints (k : Type u) [Field k] [NeZero (2 : k)] :
    ∃ (U : Over (base k))
      (p : (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj U ⟶
        sheafOfPoints k),
      (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} p.hom ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over (base k)) p.hom ∧
          AlgebraicGeometry.IsReduced U.left := sorry

/-- The formal disk, as an algebraic space, is reduced. -/
instance instIsReduced_formalDisk (k : Type u) [Field k] :
    IsReduced (ofOver (formalDisk k)) := sorry

/-- The formal disk, as an algebraic space, is quasi-separated. -/
instance instIsQuasiSeparated_formalDisk (k : Type u) [Field k] :
    IsQuasiSeparated (ofOver (formalDisk k)) := sorry

/-- The pre-relation on `Y` with source `R = Y`, first projection `t = -1`, and
second projection `s = 1`. -/
def involutionPreRelation (k : Type u) [Field k] :
    Scheme.PreRelation (formalDisk k) :=
  Scheme.PreRelation.ofHom (prod.lift (formalDiskNeg k) (𝟙 (formalDisk k)))

/-- The defining map of `involutionPreRelation k` is the pair `(-1, 1)`. -/
theorem involutionPreRelation_hom (k : Type u) [Field k] :
    (involutionPreRelation k).hom =
      prod.lift (formalDiskNeg k) (𝟙 (formalDisk k)) := sorry

/-- The first projection of `involutionPreRelation k` is `-1`. -/
theorem involutionPreRelation_t (k : Type u) [Field k] :
    (involutionPreRelation k).t = formalDiskNeg k := sorry

/-- The second projection of `involutionPreRelation k` is the identity. -/
theorem involutionPreRelation_s (k : Type u) [Field k] :
    (involutionPreRelation k).s = 𝟙 (formalDisk k) := sorry

/-- The coordinate and negative-coordinate maps from the formal disk to the involution
quotient agree after pullback along every field-valued point. -/
@[stacks 048Z]
theorem eq_on_fieldValuedPoints (k : Type u) [Field k] [NeZero (2 : k)]
    (K : Type u) [Field K] (σ : Spec (.of K) ⟶ base k)
    (p : Over.mk σ ⟶ formalDisk k) :
    (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map p ≫ fromDisk k =
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map p ≫
        fromDiskNeg k := sorry

/-- The coordinate and negative-coordinate maps from the formal disk to the involution
quotient are unequal. -/
@[stacks 048Z]
theorem fromDisk_ne_fromDiskNeg (k : Type u) [Field k] [NeZero (2 : k)] :
    fromDisk k ≠ fromDiskNeg k := sorry

/-- Every geometric point of the formal disk equalizes the identity and negation
after postcomposition with the coordinate-induced map to the involution quotient. -/
@[stacks 048Z]
theorem eq_on_geometricPoints (k : Type u) [Field k] [NeZero (2 : k)]
    (K : Type u) [Field K] [IsAlgClosed K] (σ : Spec (.of K) ⟶ base k)
    (p : Over.mk σ ⟶ formalDisk k) :
    (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map
        (p ≫ (involutionPreRelation k).s) ≫ fromDisk k =
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map
        (p ≫ (involutionPreRelation k).t) ≫ fromDisk k := sorry

/-- The identity and negation on the formal disk induce unequal morphisms after
postcomposition with the coordinate-induced map to the involution quotient. -/
@[stacks 048Z]
theorem not_t_fromDisk_eq_s_fromDisk (k : Type u) [Field k] [NeZero (2 : k)] :
    (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map
        (involutionPreRelation k).t ≫ fromDisk k ≠
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map
        (involutionPreRelation k).s ≫ fromDisk k := sorry

end AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution
