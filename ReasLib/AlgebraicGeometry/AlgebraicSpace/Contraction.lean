module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Types
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.Complement
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Reduction
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FormalModification

/-!
# Standing data for Artin contractions

A locally Noetherian base, an algebraic space locally of finite type, a closed
subset of its points, a locally Noetherian formal algebraic space whose
canonical reduction is locally of finite type, and a formal modification from
the completion along that closed subset.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Standing contraction data over a locally Noetherian scheme: an algebraic
space `X'` locally of finite type over `S`, a closed subset `T'` of
`Points X'`, a locally Noetherian formal algebraic space `W` over `S` with
reduction given by `FormalAlgebraicSpace.ReductionData` locally of finite type
over `S`, and a formal modification `g : completionAlong X' T' ⟶ W`. The
complementary open `U'` with
`Set.range (Points.map (openComplementι X' T')) = (T' : Set (Points X'))ᶜ`
is derived as `openComplementAlong X' T'`. -/
structure ContractionSituation (S : Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian S] where
  /-- The algebraic space `X'` over `S`. -/
  X' : AlgebraicSpace S
  /-- `X'` is locally of finite type over `S`. -/
  [locallyOfFiniteType_X' : LocallyOfFiniteType (SchemeRealization.toBase X')]
  /-- `X'` is locally Noetherian, so `completionAlong X' T'` is a locally
  Noetherian formal algebraic space. -/
  [isLocallyNoetherian_X' : IsLocallyNoetherian X']
  /-- The closed subset `T' ⊂ Points X'`. -/
  T' : Closeds (Points X')
  /-- The formal algebraic space `W` over `S`. -/
  W : (Over S)ᵒᵖ ⥤ Type u
  /-- `W` is a formal algebraic space. -/
  [isFormal_W : FormalAlgebraicSpace.IsFormalAlgebraicSpace W]
  /-- `W` is locally Noetherian. -/
  [isLocallyNoetherian_W : FormalAlgebraicSpace.IsLocallyNoetherian W]
  /-- Explicit data for the canonical algebraic-space reduction `W_red`. -/
  reductionData_W : FormalAlgebraicSpace.ReductionData W
  /-- `W_red` is locally of finite type over `S`. -/
  [locallyOfFiniteType_red :
    LocallyOfFiniteType (SchemeRealization.toBase reductionData_W.space)]
  /-- The formal modification `g : completionAlong X' T' ⟶ W`. -/
  g : completionAlong X' T' ⟶ W
  /-- `g` is locally of finite type. -/
  [locallyOfFiniteType_g : FormalAlgebraicSpace.LocallyOfFiniteType g]
  /-- `g` is a formal modification. -/
  [isFormalModification : FormalAlgebraicSpace.FormalModification g]

namespace ContractionSituation

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]

/-- Package an algebraic space locally of finite type over `S`, a closed
subset of its points, a locally Noetherian formal algebraic space with explicit
reduction data locally of finite type over `S`, and a formal modification from
the completion along the closed subset. -/
def ofData (X' : AlgebraicSpace S)
    [LocallyOfFiniteType (SchemeRealization.toBase X')]
    [IsLocallyNoetherian X'] (T' : Closeds (Points X'))
    (W : (Over S)ᵒᵖ ⥤ Type u)
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace W]
    [FormalAlgebraicSpace.IsLocallyNoetherian W]
    (R : FormalAlgebraicSpace.ReductionData W)
    [locallyOfFiniteType_red : LocallyOfFiniteType (SchemeRealization.toBase R.space)]
    (g : completionAlong X' T' ⟶ W)
    [FormalAlgebraicSpace.LocallyOfFiniteType g]
    [FormalAlgebraicSpace.FormalModification g] :
    ContractionSituation S where
  X' := X'
  T' := T'
  W := W
  reductionData_W := R
  locallyOfFiniteType_red := inferInstance
  g := g

/-- A contraction situation records that `X'` is locally of finite type and
locally Noetherian, that `W` is a locally Noetherian formal algebraic space
whose canonical reduction is locally of finite type over `S`, and that `g` is
a formal modification. -/
theorem specData (σ : ContractionSituation S) :
    LocallyOfFiniteType (SchemeRealization.toBase σ.X') ∧ IsLocallyNoetherian σ.X' ∧
      FormalAlgebraicSpace.IsFormalAlgebraicSpace σ.W ∧
      @FormalAlgebraicSpace.IsLocallyNoetherian S σ.W σ.isFormal_W ∧
      LocallyOfFiniteType (SchemeRealization.toBase
        (@FormalAlgebraicSpace.ReductionData.space S σ.W σ.isFormal_W σ.reductionData_W)) ∧
      @FormalAlgebraicSpace.FormalModification S (completionAlong σ.X' σ.T')
        σ.W σ.g
        (instIsFormalAlgebraicSpace_completionAlong σ.X' σ.T') σ.isFormal_W
        (@instIsLocallyNoetherian_completionAlong S σ.X'
          σ.isLocallyNoetherian_X' σ.T')
        σ.isLocallyNoetherian_W σ.locallyOfFiniteType_g :=
  sorry

/-- The open subspace `U' ⊂ X'` with `|U'| = |X'| \ T'`. -/
@[reducible] def openComplement (σ : ContractionSituation S) : AlgebraicSpace S :=
  openComplementAlong σ.X' σ.T'

/-- The open immersion of the complement of `T'` into `X'`. -/
abbrev openComplementι (σ : ContractionSituation S) :
    σ.openComplement ⟶ σ.X' :=
  AlgebraicSpace.openComplementι σ.X' σ.T'

/-- The open complement of `T'` is `openComplementAlong` of the stored data. -/
theorem openComplement_eq (σ : ContractionSituation S) :
    σ.openComplement = openComplementAlong σ.X' σ.T' :=
  sorry

/-- The image of `|U'|` in `|X'|` is the complement of `T'`. -/
theorem openComplement_pointsSet (σ : ContractionSituation S) :
    Set.range (Points.map σ.openComplementι) = (σ.T' : Set (Points σ.X'))ᶜ :=
  sorry

/-- The formal completion `X'_{/T'}` of `X'` along `T'`. -/
abbrev completion (σ : ContractionSituation S) : (Over S)ᵒᵖ ⥤ Type u :=
  completionAlong σ.X' σ.T'

/-- The stored completion is `completionAlong` of `X'` along `T'`. -/
theorem completion_eq (σ : ContractionSituation S) :
    σ.completion = completionAlong σ.X' σ.T' :=
  sorry

end ContractionSituation

end AlgebraicGeometry.AlgebraicSpace
