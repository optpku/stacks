module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.Monoidal.Adjunction.ProjectionFormula
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projection formulas and base change

Projection-formula mates commute with right mates of monoidal squares.  Monoidality of the square
is expressed by Mathlib's `NatTrans.IsMonoidal`, rather than by an objectwise family of tensor
comparisons and a separate compatibility square.
-/

@[expose] public section

open CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.OplaxMonoidal

noncomputable section

universe uX uX' uY uY' vX vX' vY vY'

namespace CategoryTheory

variable {DX : Type uX} [Category.{vX} DX]
variable {DX' : Type uX'} [Category.{vX'} DX']
variable {DY : Type uY} [Category.{vY} DY]
variable {DY' : Type uY'} [Category.{vY'} DY']
variable [MonoidalCategory DX] [MonoidalCategory DX']
variable [MonoidalCategory DY] [MonoidalCategory DY']
variable (Lf : DY ⥤ DX) (Lf' : DY' ⥤ DX')
variable (Lg : DY ⥤ DY') (Lg' : DX ⥤ DX')
variable (Rf : DX ⥤ DY) (Rf' : DX' ⥤ DY')
variable [Lf.Monoidal] [Lf'.Monoidal] [Lg.Monoidal] [Lg'.Monoidal]
variable (adj_f : Lf ⊣ Rf) (adj_f' : Lf' ⊣ Rf')
variable (squareIso : Lg ⋙ Lf' ≅ Lf ⋙ Lg')
variable [NatTrans.IsMonoidal squareIso.hom]

/-- The projection-formula mates commute with the canonical right base-change mates of a
monoidal square. -/
theorem projectionFormulaMate_baseChange_commSq
    (E : DX) (K : DY) :
    CommSq
      (Lg.map (adj_f.projectionFormulaMate K E))
      (δ Lg K (Rf.obj E) ≫
        (𝟙 (Lg.obj K) ⊗ₘ
          derivedBaseChangeMap Lf Lf' Lg Lg' Rf Rf' adj_f adj_f' squareIso E))
      (derivedBaseChangeMap Lf Lf' Lg Lg' Rf Rf' adj_f adj_f' squareIso
          (Lf.obj K ⊗ E) ≫
        Rf'.map
          (δ Lg' (Lf.obj K) E ≫
            (squareIso.inv.app K ⊗ₘ 𝟙 (Lg'.obj E))))
      (adj_f'.projectionFormulaMate (Lg.obj K) (Lg'.obj E)) := sorry

/-- Projection-formula mates commute with any chosen base-change components satisfying the
canonical adjunction-transpose specification. -/
theorem projectionFormulaMate_baseChange_commSq_of_isDerivedBaseChangeMap
    (E : DX) (K : DY)
    (etaE : Lg.obj (Rf.obj E) ⟶ Rf'.obj (Lg'.obj E))
    (etaTensor :
      Lg.obj (Rf.obj (Lf.obj K ⊗ E)) ⟶
        Rf'.obj (Lg'.obj (Lf.obj K ⊗ E)))
    (hEtaE : IsDerivedBaseChangeMap
      Lf Lf' Lg Lg' Rf Rf' adj_f adj_f' squareIso E etaE)
    (hEtaTensor : IsDerivedBaseChangeMap
      Lf Lf' Lg Lg' Rf Rf' adj_f adj_f' squareIso
        (Lf.obj K ⊗ E) etaTensor) :
    CommSq
      (Lg.map (adj_f.projectionFormulaMate K E))
      (δ Lg K (Rf.obj E) ≫ (𝟙 (Lg.obj K) ⊗ₘ etaE))
      (etaTensor ≫
        Rf'.map
          (δ Lg' (Lf.obj K) E ≫
            (squareIso.inv.app K ⊗ₘ 𝟙 (Lg'.obj E))))
      (adj_f'.projectionFormulaMate (Lg.obj K) (Lg'.obj E)) := sorry

/-- The left projection-formula mates commute with the canonical right base-change mates of a
monoidal square. This is the tensor order used by the Stacks projection-formula map. -/
@[stacks 0B6B "canonical left base-change mates"]
theorem leftProjectionFormulaMate_baseChange_commSq
    (E : DX) (K : DY) :
    CommSq
      (Lg.map (adj_f.leftProjectionFormulaMate E K))
      (δ Lg (Rf.obj E) K ≫
        (derivedBaseChangeMap Lf Lf' Lg Lg' Rf Rf' adj_f adj_f' squareIso E ⊗ₘ
          𝟙 (Lg.obj K)))
      (derivedBaseChangeMap Lf Lf' Lg Lg' Rf Rf' adj_f adj_f' squareIso
          (E ⊗ Lf.obj K) ≫
        Rf'.map
          (δ Lg' E (Lf.obj K) ≫
            (𝟙 (Lg'.obj E) ⊗ₘ squareIso.inv.app K)))
      (adj_f'.leftProjectionFormulaMate (Lg'.obj E) (Lg.obj K)) := sorry

/-- Left projection-formula mates commute with any chosen base-change components satisfying the
canonical adjunction-transpose specification. -/
theorem leftProjectionFormulaMate_baseChange_commSq_of_isDerivedBaseChangeMap
    (E : DX) (K : DY)
    (etaE : Lg.obj (Rf.obj E) ⟶ Rf'.obj (Lg'.obj E))
    (etaTensor :
      Lg.obj (Rf.obj (E ⊗ Lf.obj K)) ⟶
        Rf'.obj (Lg'.obj (E ⊗ Lf.obj K)))
    (hEtaE : IsDerivedBaseChangeMap
      Lf Lf' Lg Lg' Rf Rf' adj_f adj_f' squareIso E etaE)
    (hEtaTensor : IsDerivedBaseChangeMap
      Lf Lf' Lg Lg' Rf Rf' adj_f adj_f' squareIso
        (E ⊗ Lf.obj K) etaTensor) :
    CommSq
      (Lg.map (adj_f.leftProjectionFormulaMate E K))
      (δ Lg (Rf.obj E) K ≫ (etaE ⊗ₘ 𝟙 (Lg.obj K)))
      (etaTensor ≫
        Rf'.map
          (δ Lg' E (Lf.obj K) ≫
            (𝟙 (Lg'.obj E) ⊗ₘ squareIso.inv.app K)))
      (adj_f'.leftProjectionFormulaMate (Lg'.obj E) (Lg.obj K)) := sorry

end CategoryTheory
