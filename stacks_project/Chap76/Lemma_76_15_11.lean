module

public import stacks_project.Chap76.Lemma_76_15_11_Localization
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

noncomputable section

universe u

variable {S : Scheme.{u}}
variable {X Z U V : AlgebraicSpace S}
variable (fVZ : V ⟶ Z) (fUX : U ⟶ X)
variable [Etale fVZ] [Etale fUX]

section
variable (fVU : V ⟶ U) (h : Z ⟶ X)
variable [FormallyUnramified h]
variable (sq : CommSq fVU fVZ fUX h)

/- Lemma 76.15.11 (1): Let `S` be a scheme. Let `h : Z ⟶ X` be a formally
unramified morphism of algebraic spaces over `S`, and let `V ⟶ U` over
`Z ⟶ X` be a commutative square with étale vertical arrows. Then `V ⟶ U` is
formally unramified. -/
@[stacks 060D]
#check
  (FormallyUnramified.of_etaleCommSq fVU fVZ fUX h sq : FormallyUnramified fVU)
end

variable {Z' V' : AlgebraicSpace S}
variable (iZ : Z ⟶ Z') (fZ : Z' ⟶ X) (iV : V ⟶ V') (fV : V' ⟶ U)
variable [IsUniversalFirstOrder iZ fZ] [IsUniversalFirstOrder iV fV]
variable [FormallyUnramified (iZ ≫ fZ)] [FormallyUnramified (iV ≫ fV)]
variable (sqComp : CommSq fVZ (iV ≫ fV) (iZ ≫ fZ) fUX)

/- Lemma 76.15.11 (2): If `Z'` is a universal first-order thickening of `Z`
over `X` and `V'` is a universal first-order thickening of `V` over `U`, then
the canonical comparison `V' ⟶ Z'` is étale. -/
@[stacks 060D]
#check
  (IsUniversalFirstOrder.comparison_etale iZ fZ iV fV fVZ fUX sqComp :
    Etale (IsUniversalFirstOrder.comparison iV fV iZ fZ fVZ fUX sqComp))

/- Lemma 76.15.11 (3): In particular the canonical map
`(Modules.pullback fVZ).obj (Hom.conormalSheaf iZ) ⟶ Hom.conormalSheaf iV` is an
isomorphism, so `C_{Z/X}` restricted along `V ⟶ Z` is identified with
`C_{V/U}`. -/
@[stacks 060D]
#check
  (IsUniversalFirstOrder.conormalMap_isIso_of_etale iZ fZ iV fV fVZ fUX sqComp :
    IsIso (IsUniversalFirstOrder.conormalMap iV fV iZ fZ fVZ fUX sqComp))
