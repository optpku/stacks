module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Deformation.Perturbation.Etale
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.Hom.Deformation

noncomputable section

universe u

/- Lemma 76.17.8: Let `S` be a scheme. Consider a commutative diagram of first-order
thickenings `(T₂ ⊂ T₂') ⟶ (X₂ ⊂ X₂')` over `(T₁ ⊂ T₁') ⟶ (X₁ ⊂ X₁')` and a
commutative diagram `X₂' ⟶ B₂`, `X₁' ⟶ B₁` of algebraic spaces over `S`, with
`X₂ ⟶ X₁` and `B₂ ⟶ B₁` étale. For any `𝒪_{T₁}`-linear map
`θ₁ : a₁^* Ω_{X₁/B₁} ⟶ C_{T₁/T₁'}`, let `θ₂` be the composite of the canonical
étale identification `a₂^* Ω_{X₂/B₂} ≅ h^* a₁^* Ω_{X₁/B₁}`, the pullback `h^* θ₁`,
and the conormal map of the `T`-square. Then the diagram of Remark 76.17.3 actions
`(θ₂ · a₂')` and `(θ₁ · a₁')` commutes. -/
@[stacks 0CK8] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.Deformation.perturbation_commSq_of_etale :
    ∀ {S : Scheme.{u}}
    {B1 B2 T1 T1' T2 T2' X1 X1' X2 X2' : AlgebraicSpace S}
    (sB : B2 ⟶ B1)
    (sX1 : X1 ⟶ B1) (sX1' : X1' ⟶ B1)
    (sX2 : X2 ⟶ B2) (sX2' : X2' ⟶ B2)
    (iT1 : T1 ⟶ T1') (iX1 : X1 ⟶ X1') (iT2 : T2 ⟶ T2') (iX2 : X2 ⟶ X2')
    (a1 : T1 ⟶ X1) (a1' : T1' ⟶ X1') (a2 : T2 ⟶ X2) (a2' : T2' ⟶ X2')
    (h : T2 ⟶ T1) (h' : T2' ⟶ T1') (f : X2 ⟶ X1) (f' : X2' ⟶ X1')
    [IsFirstOrderThickening iT1] [IsFirstOrderThickening iX1]
    [IsFirstOrderThickening iT2] [IsFirstOrderThickening iX2]
    [Etale f] [Etale sB]
    (sqA1 : CommSq a1 iT1 iX1 a1') (sqA2 : CommSq a2 iT2 iX2 a2')
    (sqT : CommSq h iT2 iT1 h') (sqX : CommSq f iX2 iX1 f')
    (sq0 : CommSq a2 h f a1) (sq1 : CommSq a2' h' f' a1')
    (sqS : CommSq f' sX2' sX1' sB)
    (hX1 : iX1 ≫ sX1' = sX1) (hX2 : iX2 ≫ sX2' = sX2)
    (θ1 : (Modules.pullback a1).obj (relativeDifferentials sX1) ⟶ Hom.conormalSheaf iT1)
    (b1' : T1' ⟶ X1') (b2' : T2' ⟶ X2')
    (hb1 : IsPerturbation sX1 (a1' ≫ sX1') sX1' iT1 iX1 a1 a1' sqA1 θ1 b1')
    (hb2 : IsPerturbation sX2 (a2' ≫ sX2') sX2' iT2 iX2 a2 a2' sqA2
      (pullbackPerturbationMap sB f h a1 a2 sX1 sX2 iT1 iT2 h'
        (by simpa only [hX1, hX2] using sqX.vert_comp sqS) sq0 sqT θ1)
      b2'),
    CommSq b2' h' f' b1')
