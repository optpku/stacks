module

public import stacks_project.Chap67.Lemma_67_33_3_ResidueFieldTrdeg
public import stacks_project.Chap82.Definition_82_5_2_AssociatedCycle
public import stacks_project.Chap82.Lemma_82_10_4_Pullback
public import stacks_project.Chap82.Lemma_82_17_3_Pullback
public import stacks_project.Chap82.Lemma_82_17_3_Torsor
import StacksCheckRecall

/-!
# Lemma 82.17.3

In Situation 82.2.1, for good `X / B` and an invertible `𝒪_X`-module `L`, the
relative spectrum `q : T = Spec_X(⨁_{n ∈ ℤ} L^{⊗ n}) ⟶ X` is the canonical
`G_m`-torsor of `L`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open IsLocalRing TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/- Lemma 82.17.3 (1): the morphism `q = gmTorsorπ L` is surjective, smooth,
affine, and of relative dimension `1`. -/
@[stacks 0EQG] #check instSurjective_gmTorsorπ
@[stacks 0EQG] #check instSmooth_gmTorsorπ
@[stacks 0EQG] #check instAffine_gmTorsorπ
@[stacks 0EQG] #check instRelativeDimension_gmTorsorπ

/- Lemma 82.17.3 (2): there is an isomorphism `α : q^* L ≅ 𝒪_T`. -/
@[stacks 0EQG] #check gmTorsorTriv

/- Lemma 82.17.3 (3): formation of `(q : T ⟶ X, α)` commutes with base change. -/
@[stacks 0EQG] #check gmTorsorPullbackIso
@[stacks 0EQG] #check gmTorsorTriv_pullback

/-- Lemma 82.17.3 (4): In Situation 82.2.1, for good `X / B` and invertible `L`,
the flat pullback `q^* : Z_k(X) → Z_{k+1}(T)` is injective. -/
@[stacks 0EQG]
theorem gmTorsorπ_flatPullbackHom_injective {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (L : X.Modules) [isInvertibleObject L] (k : ℤ) :
    Function.Injective
      (Hom.flatPullbackHom f (gmTorsorπ L ≫ f) δ (gmTorsorπ L) 1 rfl k) :=
  sorry

/- Lemma 82.17.3 (5): if `Z ⊂ X` is an integral closed subspace, then
`q⁻¹(Z) ⊂ T` is an integral closed subspace. -/
@[stacks 0EQG] #check instIsIntegral_inverseImage_gmTorsorπ

/-- Lemma 82.17.3 (6): if `Z ⊂ X` has `δ`-dimension `≤ k`, then `q⁻¹(Z)` has
`δ`-dimension `≤ k+1`. -/
@[stacks 0EQG]
theorem gmTorsorπ_inverseImage_deltaDimension_le {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (L : X.Modules) [isInvertibleObject L] (Z : ClosedSubspace X) (k : ℤ)
    (hZ : Hom.closedSubspaceDeltaDimension f δ Z ≤ (k : EInt)) :
    Hom.closedSubspaceDeltaDimension (gmTorsorπ L ≫ f) δ
        (Z.inverseImage (gmTorsorπ L)) ≤ (k + 1 : EInt) :=
  sorry

/-- Lemma 82.17.3 (6): if `Z ⊂ X` is a closed subspace of `δ`-dimension `≤ k`,
then `q^*[Z]_k = [q⁻¹(Z)]_{k+1}`. -/
@[stacks 0EQG]
theorem gmTorsorπ_closedSubspaceCycle {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (L : X.Modules) [isInvertibleObject L] (Z : ClosedSubspace X) (k : ℤ)
    (hZ : Hom.closedSubspaceDeltaDimension f δ Z ≤ (k : EInt)) :
    Hom.flatPullback f (gmTorsorπ L ≫ f) δ (gmTorsorπ L) 1 rfl k
        (Hom.closedSubspaceCycle f δ Z k hZ) =
      Hom.closedSubspaceCycle (gmTorsorπ L ≫ f) δ
        (Z.inverseImage (gmTorsorπ L)) (k + 1)
        (gmTorsorπ_inverseImage_deltaDimension_le f δ L Z k hZ) :=
  sorry

/- Lemma 82.17.3 (7): if `ξ' ∈ |T|` is the generic point of the fibre of
`|T| ⟶ |X|` over `ξ`, then `𝒪_{X,ξ}^h → 𝒪_{T,ξ'}^h` is the named map
`henselianMap`, which is local, flat, identifies maximal ideals, and has
purely transcendental residue-field extension. -/
@[stacks 0EQG] #check henselianMap
@[stacks 0EQG] #check instIsLocalHom_henselianMap
@[stacks 0EQG] #check gmTorsorπ_henselianMap_flat
@[stacks 0EQG] #check gmTorsorπ_henselianMap_maximalIdeal
@[stacks 0EQG] #check gmTorsorπ_henselianMap_isPurelyTranscendental

/-- Lemma 82.17.3 (7): the residue-field extension along `q` at the generic
point of the fibre has transcendence degree `1`. -/
@[stacks 0EQG]
theorem gmTorsorπ_residueFieldTrdeg {X : AlgebraicSpace S}
    (L : X.Modules) [isInvertibleObject L] [IsDecent X]
    (ξ : Points X) (ξ' : Points (gmTorsor L))
    (hξ' : Points.map (gmTorsorπ L) ξ' = ξ ∧
      IsGenericPoint ξ' (closure (Points.map (gmTorsorπ L) ⁻¹' {ξ}))) :
    residueFieldTrdegAt (gmTorsorπ L) ξ' = 1 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
