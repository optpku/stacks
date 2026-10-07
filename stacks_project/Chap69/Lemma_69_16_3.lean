module

public import stacks_project.Chap69.Lemma_69_16_2_ToSpec
public import stacks_project.Chap69.Lemma_69_16_3_BaseChange
public import stacks_project.Chap69.Situation_69_16_1

/-!
# Lemma 69.16.3

In Situation 69.16.1, affine morphisms of algebraic spaces preserve vanishing of
`H¹` on quasi-coherent modules. Base change of `X` along `Spec A' ⟶ Spec A`
is affine, and recovers `A'` as global sections.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 69.16.3 (1): In Situation 69.16.1, if `f : X' ⟶ X` is affine, then
`H¹(X', F') = 0` for every quasi-coherent `𝒪_{X'}`-module `F'`. -/
@[stacks 07V0]
theorem hasVanishingH1_of_affine {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    [IsQuasiCompact X] [IsQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasVanishingH1 X]
    [HasSheafify (smallEtaleTopology X') AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X') AddCommGrpCat.{u})]
    (f : X' ⟶ X) [Affine f] : HasVanishingH1 X' :=
  sorry

/-- First cohomology of a quasi-coherent module vanishes after an affine morphism
from Situation 69.16.1. -/
theorem cohomology_isZero_of_affine {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    [IsQuasiCompact X] [IsQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasVanishingH1 X]
    [HasSheafify (smallEtaleTopology X') AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X') AddCommGrpCat.{u})]
    (f : X' ⟶ X) [Affine f] (F : Modules X')
    (hF : quasiCoherentModuleProperty X' F) : IsZero (cohomology X' F 1) :=
  sorry

/-- Lemma 69.16.3 (2): For an `A`-algebra `A'`, the projection
`X ×_{Spec A} Spec A' ⟶ X` is affine. -/
@[stacks 07V0]
instance affine_baseChangeSpecHom {S : Scheme.{u}} (X : AlgebraicSpace S)
    {A' : CommRingCat.{u}} (φ : globalSectionsRing X ⟶ A') :
    Affine (baseChangeSpecHom X φ) :=
  affine_pullback_snd (specMapToGamma X φ) (toSpecGamma X)

/-- Lemma 69.16.3 (3): For an `A`-algebra `A'`, one has
`Γ(X ×_{Spec A} Spec A', 𝒪) ≅ A'`. -/
@[stacks 07V0]
theorem globalSectionsRing_baseChangeSpec {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasVanishingH1 X] {A' : CommRingCat.{u}} (φ : globalSectionsRing X ⟶ A') :
    Nonempty (globalSectionsRing (baseChangeSpec X φ) ≅ A') :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
