module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Admissible
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ResolutionProperty
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute

/-!
# Finite nested closed filtrations with admissible resolution blowups

A finite filtration consists of nested closed subspaces of an algebraic space,
each of finite presentation over the ambient space, beginning with a
thickening and ending empty, together with admissible blowups of the
successive differences that have the resolution property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A terminating nested sequence of closed subspaces of `X`, each of finite
presentation over `X`, with first stage a thickening and last stage empty,
together with `(Z_i \ Z_{i+1})`-admissible blowups that have the resolution
property. -/
structure FiniteClosedResolutionBlowupFiltration {S : Scheme.{u}}
    (X : AlgebraicSpace S) where
  /-- An index `t` such that the last closed stage `Z_t` is empty. -/
  bound : ℕ
  /-- The nested closed subspaces `Z_0, …, Z_t`. -/
  closedStage : Fin (bound + 1) → ClosedSubspace X
  /-- The blowup space `Z'_i` of the `i`-th closed stage. -/
  blowupStage : Fin bound → AlgebraicSpace S
  /-- The blowup morphism `Z'_i ⟶ Z_i`. -/
  blowup (i : Fin bound) : blowupStage i ⟶ (closedStage i.castSucc).X
  /-- An open subspace of `Z_i` representing the difference `Z_i \ Z_{i+1}`. -/
  diffOpen (i : Fin bound) : OpenSubspace (closedStage i.castSucc).X
  /-- The scheme-theoretic inclusion `Z_{i+1} ⟶ Z_i` of successive closed stages. -/
  stageIncl (i : Fin bound) : (closedStage i.succ).X ⟶ (closedStage i.castSucc).X
  /-- The inclusion `Z_{i+1} ⟶ Z_i` lies over `X`, recovering `Z_i ⊃ Z_{i+1}`. -/
  stageIncl_ι (i : Fin bound) :
    stageIncl i ≫ (closedStage i.castSucc).ι = (closedStage i.succ).ι
  /-- Support nesting `|Z_0| ⊃ ⋯ ⊃ |Z_t|`, implied by the scheme-theoretic
  inclusions. -/
  antitone_pointsSet : Antitone fun i ↦ (closedStage i).pointsSet
  /-- Each closed immersion `Z_i ⟶ X` is of finite presentation. -/
  finitePresentation_closedStage (i : Fin (bound + 1)) :
    FinitePresentation (closedStage i).ι
  /-- The first closed stage `Z_0 ⊂ X` is a thickening. -/
  isThickening_zero : IsThickening (closedStage 0).ι
  /-- The last closed stage occupies none of `|X|`, encoding `Z_t = ∅`. -/
  pointsSet_last : (closedStage (Fin.last bound)).pointsSet = ∅
  /-- The stored open of `Z_i` occupies the successive difference `Z_i \ Z_{i+1}`. -/
  diffOpen_pointsSet (i : Fin bound) :
    (diffOpen i).pointsSet =
      Points.map (closedStage i.castSucc).ι ⁻¹'
        ((closedStage i.castSucc).pointsSet \ (closedStage i.succ).pointsSet)
  /-- Each blowup `Z'_i ⟶ Z_i` is `(Z_i \ Z_{i+1})`-admissible. -/
  isAdmissibleBlowup_blowup (i : Fin bound) :
    IsAdmissibleBlowup (diffOpen i) (blowup i)
  /-- Each blowup space `Z'_i` has the resolution property. -/
  hasResolutionProperty_blowupStage (i : Fin bound) :
    SheafOfModules.HasResolutionProperty (structureSheaf (blowupStage i))

namespace FiniteClosedResolutionBlowupFiltration

/-- Assemble a finite closed resolution-blowup filtration from nested closed
stages, blowups, difference opens, successive inclusions, and their compatibility laws. -/
def ofStages {S : Scheme.{u}} {X : AlgebraicSpace S} (bound : ℕ)
    (closedStage : Fin (bound + 1) → ClosedSubspace X)
    (blowupStage : Fin bound → AlgebraicSpace S)
    (blowup : ∀ i, blowupStage i ⟶ (closedStage i.castSucc).X)
    (diffOpen : ∀ i, OpenSubspace (closedStage i.castSucc).X)
    (stageIncl : ∀ i : Fin bound, (closedStage i.succ).X ⟶ (closedStage i.castSucc).X)
    (stageIncl_ι : ∀ i : Fin bound, stageIncl i ≫ (closedStage i.castSucc).ι = (closedStage i.succ).ι)
    (antitone_pointsSet : Antitone fun i ↦ (closedStage i).pointsSet)
    (finitePresentation_closedStage : ∀ i, FinitePresentation (closedStage i).ι)
    (isThickening_zero : IsThickening (closedStage 0).ι)
    (pointsSet_last : (closedStage (Fin.last bound)).pointsSet = ∅)
    (diffOpen_pointsSet : ∀ i : Fin bound, (diffOpen i).pointsSet =
      Points.map (closedStage i.castSucc).ι ⁻¹'
        ((closedStage i.castSucc).pointsSet \ (closedStage i.succ).pointsSet))
    (isAdmissibleBlowup_blowup : ∀ i, IsAdmissibleBlowup (diffOpen i) (blowup i))
    (hasResolutionProperty_blowupStage : ∀ i, SheafOfModules.HasResolutionProperty (structureSheaf (blowupStage i))) :
    FiniteClosedResolutionBlowupFiltration X where
  bound := bound
  closedStage := closedStage
  blowupStage := blowupStage
  blowup := blowup
  diffOpen := diffOpen
  stageIncl := stageIncl
  stageIncl_ι := stageIncl_ι
  antitone_pointsSet := antitone_pointsSet
  finitePresentation_closedStage := finitePresentation_closedStage
  isThickening_zero := isThickening_zero
  pointsSet_last := pointsSet_last
  diffOpen_pointsSet := diffOpen_pointsSet
  isAdmissibleBlowup_blowup := isAdmissibleBlowup_blowup
  hasResolutionProperty_blowupStage := hasResolutionProperty_blowupStage

/-- The bound of a filtration built by `ofStages` is the supplied bound. -/
@[simp]
theorem ofStages_bound {S : Scheme.{u}} {X : AlgebraicSpace S} (bound : ℕ)
    (closedStage : Fin (bound + 1) → ClosedSubspace X)
    (blowupStage : Fin bound → AlgebraicSpace S)
    (blowup : ∀ i, blowupStage i ⟶ (closedStage i.castSucc).X)
    (diffOpen : ∀ i, OpenSubspace (closedStage i.castSucc).X)
    (stageIncl : ∀ i : Fin bound, (closedStage i.succ).X ⟶ (closedStage i.castSucc).X)
    (stageIncl_ι : ∀ i : Fin bound, stageIncl i ≫ (closedStage i.castSucc).ι = (closedStage i.succ).ι)
    (antitone_pointsSet : Antitone fun i ↦ (closedStage i).pointsSet)
    (finitePresentation_closedStage : ∀ i, FinitePresentation (closedStage i).ι)
    (isThickening_zero : IsThickening (closedStage 0).ι)
    (pointsSet_last : (closedStage (Fin.last bound)).pointsSet = ∅)
    (diffOpen_pointsSet : ∀ i : Fin bound, (diffOpen i).pointsSet =
      Points.map (closedStage i.castSucc).ι ⁻¹'
        ((closedStage i.castSucc).pointsSet \ (closedStage i.succ).pointsSet))
    (isAdmissibleBlowup_blowup : ∀ i, IsAdmissibleBlowup (diffOpen i) (blowup i))
    (hasResolutionProperty_blowupStage : ∀ i, SheafOfModules.HasResolutionProperty (structureSheaf (blowupStage i))) :
    (ofStages bound closedStage blowupStage blowup diffOpen stageIncl stageIncl_ι
      antitone_pointsSet finitePresentation_closedStage isThickening_zero
      pointsSet_last diffOpen_pointsSet isAdmissibleBlowup_blowup
      hasResolutionProperty_blowupStage).bound = bound :=
  sorry

/-- The closed stages of a filtration built by `ofStages` are the supplied stages. -/
@[simp]
theorem ofStages_closedStage {S : Scheme.{u}} {X : AlgebraicSpace S} (bound : ℕ)
    (closedStage : Fin (bound + 1) → ClosedSubspace X)
    (blowupStage : Fin bound → AlgebraicSpace S)
    (blowup : ∀ i, blowupStage i ⟶ (closedStage i.castSucc).X)
    (diffOpen : ∀ i, OpenSubspace (closedStage i.castSucc).X)
    (stageIncl : ∀ i : Fin bound, (closedStage i.succ).X ⟶ (closedStage i.castSucc).X)
    (stageIncl_ι : ∀ i : Fin bound, stageIncl i ≫ (closedStage i.castSucc).ι = (closedStage i.succ).ι)
    (antitone_pointsSet : Antitone fun i ↦ (closedStage i).pointsSet)
    (finitePresentation_closedStage : ∀ i, FinitePresentation (closedStage i).ι)
    (isThickening_zero : IsThickening (closedStage 0).ι)
    (pointsSet_last : (closedStage (Fin.last bound)).pointsSet = ∅)
    (diffOpen_pointsSet : ∀ i : Fin bound, (diffOpen i).pointsSet =
      Points.map (closedStage i.castSucc).ι ⁻¹'
        ((closedStage i.castSucc).pointsSet \ (closedStage i.succ).pointsSet))
    (isAdmissibleBlowup_blowup : ∀ i, IsAdmissibleBlowup (diffOpen i) (blowup i))
    (hasResolutionProperty_blowupStage : ∀ i, SheafOfModules.HasResolutionProperty (structureSheaf (blowupStage i))) :
    (ofStages bound closedStage blowupStage blowup diffOpen stageIncl stageIncl_ι
      antitone_pointsSet finitePresentation_closedStage isThickening_zero
      pointsSet_last diffOpen_pointsSet isAdmissibleBlowup_blowup
      hasResolutionProperty_blowupStage).closedStage = closedStage :=
  sorry

/-- The blowup morphisms of a filtration built by `ofStages` are the supplied
blowups. -/
@[simp]
theorem ofStages_blowup {S : Scheme.{u}} {X : AlgebraicSpace S} (bound : ℕ)
    (closedStage : Fin (bound + 1) → ClosedSubspace X)
    (blowupStage : Fin bound → AlgebraicSpace S)
    (blowup : ∀ i, blowupStage i ⟶ (closedStage i.castSucc).X)
    (diffOpen : ∀ i, OpenSubspace (closedStage i.castSucc).X)
    (stageIncl : ∀ i : Fin bound, (closedStage i.succ).X ⟶ (closedStage i.castSucc).X)
    (stageIncl_ι : ∀ i : Fin bound, stageIncl i ≫ (closedStage i.castSucc).ι = (closedStage i.succ).ι)
    (antitone_pointsSet : Antitone fun i ↦ (closedStage i).pointsSet)
    (finitePresentation_closedStage : ∀ i, FinitePresentation (closedStage i).ι)
    (isThickening_zero : IsThickening (closedStage 0).ι)
    (pointsSet_last : (closedStage (Fin.last bound)).pointsSet = ∅)
    (diffOpen_pointsSet : ∀ i : Fin bound, (diffOpen i).pointsSet =
      Points.map (closedStage i.castSucc).ι ⁻¹'
        ((closedStage i.castSucc).pointsSet \ (closedStage i.succ).pointsSet))
    (isAdmissibleBlowup_blowup : ∀ i, IsAdmissibleBlowup (diffOpen i) (blowup i))
    (hasResolutionProperty_blowupStage : ∀ i, SheafOfModules.HasResolutionProperty (structureSheaf (blowupStage i))) :
    (ofStages bound closedStage blowupStage blowup diffOpen stageIncl stageIncl_ι
      antitone_pointsSet finitePresentation_closedStage isThickening_zero
      pointsSet_last diffOpen_pointsSet isAdmissibleBlowup_blowup
      hasResolutionProperty_blowupStage).blowup = blowup :=
  sorry

/-- The nested inclusions, finite-presentation, thickening, emptiness, admissible
blowup, and resolution-property conditions of a finite closed
resolution-blowup filtration. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : FiniteClosedResolutionBlowupFiltration X) :
    (∀ i, F.stageIncl i ≫ (F.closedStage i.castSucc).ι = (F.closedStage i.succ).ι) ∧
      Antitone (fun i ↦ (F.closedStage i).pointsSet) ∧
      (∀ i, FinitePresentation (F.closedStage i).ι) ∧
      IsThickening (F.closedStage 0).ι ∧
      (F.closedStage (Fin.last F.bound)).pointsSet = ∅ ∧
      (∀ i, (F.diffOpen i).pointsSet =
          Points.map (F.closedStage i.castSucc).ι ⁻¹'
            ((F.closedStage i.castSucc).pointsSet \ (F.closedStage i.succ).pointsSet)) ∧
      (∀ i, IsAdmissibleBlowup (F.diffOpen i) (F.blowup i)) ∧
      ∀ i, SheafOfModules.HasResolutionProperty (structureSheaf (F.blowupStage i)) :=
  sorry

end FiniteClosedResolutionBlowupFiltration

/-- Let `S` be a scheme. Let `X` be a quasi-compact and
quasi-separated algebraic space over `S`. There exist `t ≥ 0` and nested closed
subspaces `X ⊃ Z₀ ⊃ ⋯ ⊃ Z_t = ∅` such that each `Z_i ⟶ X` is of finite
presentation, `Z₀ ⊂ X` is a thickening, and for each `i < t` there is a
`(Z_i \ Z_{i+1})`-admissible blowing up `Z'_i ⟶ Z_i` such that `Z'_i` has
the resolution property. -/
theorem exists_finiteClosedResolutionBlowupFiltration {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] :
    Nonempty (FiniteClosedResolutionBlowupFiltration X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
