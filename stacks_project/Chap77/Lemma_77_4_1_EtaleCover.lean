module

public import ReasLib.AlgebraicGeometry.Scheme.Module.CompleteDevissageOver
public import stacks_project.Chap66.«66_27_0_4_Comparison»
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_15_2
public import stacks_project.Chap71.Lemma_71_2_1_Pullback
public import stacks_project.Chap71.Lemma_71_4_1_Fiber

/-!
# Affine étale covers with complete dévissages

After an affine étale pointed base change of a finite-type morphism of algebraic
spaces, a finite-type quasi-coherent module admits complete dévissages on a
finite family of étale schemes covering the distinguished fibre.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The scheme morphism `W ⟶ Y'` over `S` associated to an étale chart
`W → X ×_Y Y'`. -/
def schemeHomToBase {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (Y' : smallEtaleSite Y) (W : smallEtaleSite (Limits.pullback f Y'.hom)) :
    W.left.left ⟶ Y'.left.left :=
  (ofOverPreimage (W.hom ≫ Limits.pullback.snd f Y'.hom)).left

/-- `schemeHomToBase f Y' W` is a morphism of schemes over `S`. -/
theorem schemeHomToBase_w {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (Y' : smallEtaleSite Y)
    (W : smallEtaleSite (Limits.pullback f Y'.hom)) :
    schemeHomToBase f Y' W ≫ Y'.left.hom = W.left.hom :=
  sorry

/-- The algebraic-space morphism associated to `schemeHomToBase f Y' W` is
`W.hom ≫ Limits.pullback.snd f Y'.hom`. -/
theorem schemeHomToBase_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (Y' : smallEtaleSite Y)
    (W : smallEtaleSite (Limits.pullback f Y'.hom)) :
    ofOverMap (Over.homMk (schemeHomToBase f Y' W) (schemeHomToBase_w f Y' W)) =
      W.hom ≫ Limits.pullback.snd f Y'.hom :=
  sorry

namespace schemeHomToBase

/-- Finite type of `X ⟶ Y` implies that each chart morphism `W ⟶ Y'` is locally
of finite type as a morphism of schemes. -/
instance instLocallyOfFiniteType {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [FiniteType f] (Y' : smallEtaleSite Y)
    (W : smallEtaleSite (Limits.pullback f Y'.hom)) :
    AlgebraicGeometry.LocallyOfFiniteType (schemeHomToBase f Y' W) :=
  sorry

end schemeHomToBase

namespace Modules

/-- The pullback of an `𝒪_X`-module to an étale scheme chart of `X ×_Y Y'`. -/
abbrev pullbackToEtaleChart {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (Y' : smallEtaleSite Y)
    (W : smallEtaleSite (Limits.pullback f Y'.hom)) (F : X.Modules) :
    W.left.left.Modules :=
  pullbackToScheme (W.hom ≫ Limits.pullback.fst f Y'.hom) F

namespace pullbackToEtaleChart

/-- Finite type of `F` is preserved by pullback to an étale scheme chart of
`X ×_Y Y'`. -/
instance instIsFiniteType {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (Y' : smallEtaleSite Y)
    (W : smallEtaleSite (Limits.pullback f Y'.hom)) (F : X.Modules)
    [F.IsFiniteType] : (pullbackToEtaleChart f Y' W F).IsFiniteType :=
  sorry

end pullbackToEtaleChart

/-- After an affine étale pointed base change, a finite-type quasi-coherent
module on an algebraic space admits complete dévissages on a finite family of
étale schemes covering the distinguished fibre. -/
theorem existsEtaleCoverWithCompleteDevissages {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [FiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y) :
    ∃ (Y' : smallEtaleSite Y) (y' : Y'.left.left),
      IsAffine Y'.left.left ∧ Points.mapOfOver Y'.hom y' = y ∧
        ∃ (n : ℕ) (W : Fin n → smallEtaleSite (Limits.pullback f Y'.hom))
          (D : ∀ i, Scheme.Modules.CompleteDevissageOver
            (schemeHomToBase f Y' (W i))
            (pullbackToEtaleChart f Y' (W i) F) y'),
          Set.range
              (Points.map
                (fiberι (Limits.pullback.snd f Y'.hom)
                  (FieldValuedPoint.ofScheme
                    (Scheme.FieldValuedPoint.residuePoint y')))) ⊆
            ⋃ i, Set.range (Points.mapOfOver (W i).hom) :=
  sorry

end Modules

end AlgebraicGeometry.AlgebraicSpace
