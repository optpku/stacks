module

public import ReasLib.AlgebraicGeometry.CompleteLocalAlgebra.Residue
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Versal
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FieldValuedPoint
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FiniteTypeOver

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor IsLocalRing
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} [IsLocallyNoetherian S]

/-- The residue-field point of the slice of `Spec(A)`. -/
def residueFieldValuedPoint (A : CompleteLocalSAlgebra S) :
    FieldValuedPoint (GroupoidsOver.slice (Over.mk A.toS)) :=
  FieldValuedPoint.of (ResidueField A.carrier) A.residueToS
    (overMap A.residueOverHom)

/-- The residue-field point of `A` has source field `κ(A)` and structure
morphism `A.residueToS`. -/
theorem residueFieldValuedPoint_spec (A : CompleteLocalSAlgebra S) :
    (residueFieldValuedPoint A).K = ResidueField A.carrier ∧
      (residueFieldValuedPoint A).structureHom = A.residueToS := ⟨rfl, rfl⟩

/-- The first stage of a formal object is compatible with a field-valued point
when the residue field of the complete local base is identified with the source
field over `S` and the corresponding objects of `X` are isomorphic over that
residue identification. -/
def StageOneCompatible {X : GroupoidsOver S} (x0 : FieldValuedPoint X)
    (ξ : GroupoidsOver.FormalObject X) : Prop :=
  ∃ (e : ResidueField ξ.base.carrier ≃+* x0.K)
    (h : residueSpecMap e ≫ ξ.base.toS = x0.structureHom)
    (α : (toFunctor x0.hom).obj (GroupoidsOver.sliceIdentityObject x0.structureHom) ≅
      ξ.stageOne),
    X.p.IsHomLift
      (CompleteLocalSAlgebra.residueStageHom e h ≫
        eqToHom (CompleteLocalSAlgebra.stageOver_zero_eq ξ.base).symm)
      α.hom

/-- Stage-one compatibility unpacks to a residue-field identification over `S`
together with an isomorphism of objects of `X` lying over that identification. -/
theorem stageOneCompatible_iff {X : GroupoidsOver S} (x0 : FieldValuedPoint X)
    (ξ : GroupoidsOver.FormalObject X) :
    StageOneCompatible x0 ξ ↔
      ∃ (e : ResidueField ξ.base.carrier ≃+* x0.K)
        (h : residueSpecMap e ≫ ξ.base.toS = x0.structureHom)
        (α : (toFunctor x0.hom).obj
            (GroupoidsOver.sliceIdentityObject x0.structureHom) ≅ ξ.stageOne),
        X.p.IsHomLift
          (CompleteLocalSAlgebra.residueStageHom e h ≫
            eqToHom (CompleteLocalSAlgebra.stageOver_zero_eq ξ.base).symm)
          α.hom := Iff.rfl

/-- A marking identifies the residue field and residue-stage object with a fixed field-valued point. -/
structure StageOneMarking {X : GroupoidsOver S} (x0 : FieldValuedPoint X)
    (ξ : GroupoidsOver.FormalObject X) where
  /-- The residue-field identification. -/
  residueEquiv : ResidueField ξ.base.carrier ≃+* x0.K
  /-- Compatibility of the residue point with the base scheme. -/
  over : residueSpecMap residueEquiv ≫ ξ.base.toS = x0.structureHom
  /-- The specified identification of residue-stage objects. -/
  iso : (toFunctor x0.hom).obj (GroupoidsOver.sliceIdentityObject x0.structureHom) ≅ ξ.stageOne
  /-- The isomorphism lies over the specified residue-field identification. -/
  homLift : X.p.IsHomLift
    (CompleteLocalSAlgebra.residueStageHom residueEquiv over ≫
      eqToHom (CompleteLocalSAlgebra.stageOver_zero_eq ξ.base).symm) iso.hom

namespace StageOneMarking

/-- Construct a marking from a residue-field identification and a lifted residue-stage isomorphism. -/
def of {X : GroupoidsOver S} {x0 : FieldValuedPoint X} {ξ : GroupoidsOver.FormalObject X}
    (e : ResidueField ξ.base.carrier ≃+* x0.K)
    (h : residueSpecMap e ≫ ξ.base.toS = x0.structureHom)
    (α : (toFunctor x0.hom).obj (GroupoidsOver.sliceIdentityObject x0.structureHom) ≅ ξ.stageOne)
    (hα : X.p.IsHomLift (CompleteLocalSAlgebra.residueStageHom e h ≫
      eqToHom (CompleteLocalSAlgebra.stageOver_zero_eq ξ.base).symm) α.hom) :
    StageOneMarking x0 ξ := ⟨e, h, α, hα⟩

/-- A marked residue-stage identification gives stage-one compatibility. -/
theorem compatible {X : GroupoidsOver S} {x0 : FieldValuedPoint X}
    {ξ : GroupoidsOver.FormalObject X} (m : StageOneMarking x0 ξ) :
    StageOneCompatible x0 ξ := ⟨m.residueEquiv, m.over, m.iso, m.homLift⟩

end StageOneMarking

/-- A complete local `S`-algebra `A` is a versal ring to `X` at a finite type
field-valued point `x0` when its residue field is identified with the source
field of `x0` over `S` and it carries a versal formal object of `X` whose first
stage is 2-isomorphic to `x0`. -/
class IsVersalRing {X : GroupoidsOver S} [AlgebraicStack X]
    (x0 : FieldValuedPoint X) [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A : CompleteLocalSAlgebra S) : Prop where
  /-- Residue field of `A` identified with the source field of `x0` over `S`. -/
  residue_iso :
    ∃ e : ResidueField A.carrier ≃+* x0.K,
      residueSpecMap e ≫ A.toS = x0.structureHom
  /-- There is a versal formal object of `X` on `A` with first stage
  2-isomorphic to `x0`. -/
  exists_versal_formalObject :
    ∃ ξ : GroupoidsOver.FormalObject X,
      ξ.base = A ∧ StageOneCompatible x0 ξ ∧ GroupoidsOver.FormalObject.IsVersal ξ

namespace IsVersalRing

/-- A versal ring supplies a residue identification and a versal formal object
compatible with `x0`. -/
theorem spec {X : GroupoidsOver S} [AlgebraicStack X]
    (x0 : FieldValuedPoint X) [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A : CompleteLocalSAlgebra S) [IsVersalRing x0 A] :
    (∃ e : ResidueField A.carrier ≃+* x0.K,
        residueSpecMap e ≫ A.toS = x0.structureHom) ∧
      ∃ ξ : GroupoidsOver.FormalObject X,
        ξ.base = A ∧ StageOneCompatible x0 ξ ∧ GroupoidsOver.FormalObject.IsVersal ξ :=
  ⟨IsVersalRing.residue_iso, IsVersalRing.exists_versal_formalObject⟩

/-- Being a versal ring is a residue identification together with a versal
formal object on `A` compatible with `x0`. -/
theorem iff {X : GroupoidsOver S} [AlgebraicStack X]
    (x0 : FieldValuedPoint X) [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A : CompleteLocalSAlgebra S) :
    IsVersalRing x0 A ↔
      (∃ e : ResidueField A.carrier ≃+* x0.K,
          residueSpecMap e ≫ A.toS = x0.structureHom) ∧
        ∃ ξ : GroupoidsOver.FormalObject X,
          ξ.base = A ∧ StageOneCompatible x0 ξ ∧ GroupoidsOver.FormalObject.IsVersal ξ :=
  ⟨fun h => ⟨h.residue_iso, h.exists_versal_formalObject⟩,
    fun h => ⟨h.1, h.2⟩⟩

end IsVersalRing

/-- The residue-field point of `A` is locally of finite type over `S`. -/
instance instLocallyOfFiniteType_residueFieldValuedPoint (A : CompleteLocalSAlgebra S) :
    AlgebraicGeometry.LocallyOfFiniteType (residueFieldValuedPoint A).structureHom :=
  A.residue_locallyOfFiniteType

/-- A complete local `S`-algebra is a versal ring to the slice of its spectrum
at the residue-field point. -/
instance instIsVersalRing_residueFieldValuedPoint (A : CompleteLocalSAlgebra S) :
    IsVersalRing (residueFieldValuedPoint A) A := sorry

/-- A finite type field-valued point of a locally finite type algebraic stack
admits a marked versal formal object. -/
theorem exists_versalFormalObject {X : GroupoidsOver S} [AlgebraicStack X]
    [IsLocallyOfFiniteType X] (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom] :
    ∃ ξ : GroupoidsOver.FormalObject X, GroupoidsOver.FormalObject.IsVersal ξ ∧
      Nonempty (StageOneMarking x0 ξ) := sorry

end AlgebraicGeometry.AlgebraicStack
