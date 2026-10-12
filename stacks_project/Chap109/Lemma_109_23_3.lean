/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap109.Lemma_109_23_3_Contraction
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

universe u

/- Lemma 109.23.3 -/
@[stacks 0E7C] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.exists_elementaryEtale_contraction :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      (f : X ⟶ ofOver (Over.mk (𝟙 S))) [IsFamily f] (s : S)
      (Y₀ : Scheme.{u}) (q₀ : Y₀ ⟶ Spec (S.residueField s)) [IsProper q₀]
      (h₀ : pullback f (residueHom s) ⟶
        ofOver (Over.mk (q₀ ≫ S.fromSpecResidueField s))),
      h₀ ≫ ofOverHomMk q₀ rfl = pullback.snd f (residueHom s) →
        IsIso (Modules.unitToPushforwardObjUnit h₀) →
          IsZero (higherDirectImageOne h₀) →
            ∃ (U : Scheme.EtaleNeighborhood S s) (Y : AlgebraicSpace S)
              (g : Y ⟶ ofOver (Over.mk U.toEtale.hom))
              (h : pullback f (etaleHom U) ⟶ Y),
              U.IsElementary ∧ IsFamily g ∧
                ∃ (h_over : h ≫ g = pullback.snd f (etaleHom U))
                  (iX : pullback (pullback.snd f (etaleHom U)) (pointHom U) ≅
                    pullback f (residueHom s))
                  (iY : pullback g (pointHom U) ≅
                    ofOver (Over.mk (q₀ ≫ S.fromSpecResidueField s))),
                  iX.hom ≫ pullback.snd f (residueHom s) =
                      pullback.snd (pullback.snd f (etaleHom U)) (pointHom U) ≫
                        ofOverHomMk
                          (Spec.map (U.toEtale.hom.residueFieldMap U.point) ≫
                            Spec.map (S.residueFieldCongr U.map_point).inv)
                          (residueFieldMap_over U) ∧
                    iX.hom ≫ h₀ = overMap h h_over (pointHom U) ≫ iY.hom)
