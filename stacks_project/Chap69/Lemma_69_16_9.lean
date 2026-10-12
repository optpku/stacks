/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap69.Definition_69_12_1_Instances
public import stacks_project.Chap69.Lemma_69_16_2_ToSpec
public import stacks_project.Chap69.Lemma_69_20_1_Tensor
public import stacks_project.Chap69.Situation_69_16_1_Cohomology

/-!
# Lemma 69.16.9

A Noetherian algebraic space with vanishing `H¹` of positive twists of every coherent
module by an invertible sheaf is a scheme, and the invertible sheaf is ample on every
representing scheme.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Modules

/-- The Zariski module on a representing scheme obtained by pulling an étale module back
along a representing isomorphism and applying `toScheme`. -/
noncomputable def toSchemeModule {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Over S}
    (e : X ≅ ofOver T) (F : X.Modules) : T.left.Modules :=
  (toScheme T).obj ((pullback e.inv).obj F)

/-- `toSchemeModule e F` is `toScheme` of the pullback of `F` along `e.inv`. -/
theorem toSchemeModule_eq {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Over S}
    (e : X ≅ ofOver T) (F : X.Modules) :
    toSchemeModule e F = (toScheme T).obj ((pullback e.inv).obj F) :=
  rfl

end Modules

/-- Lemma 69.16.9 (1): let `S` be a scheme and let `X` be a Noetherian algebraic space over
`S`. If `L` is an invertible `𝒪_X`-module such that every coherent `𝒪_X`-module `F` has some
`n ≥ 1` with `H¹(X, F ⊗ L^{⊗ n}) = 0`, then `X` is a scheme. -/
@[stacks 0D2W]
theorem isScheme_of_coherent_h1_twist_zero {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsNoetherian X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    (L : X.Modules) [isInvertibleObject L]
    (hH1 : ∀ (F : Modules X) [F.IsCoherent],
      ∃ n : ℕ, 0 < n ∧ IsZero (cohomology X (F ⊗ Modules.tensorPowerInt L n) 1)) :
    IsScheme X :=
  sorry

/-- Lemma 69.16.9 (2): under the same hypotheses, `L` is ample on every scheme representing
`X`. -/
@[stacks 0D2W]
theorem isAmpleObject_toSchemeModule_of_coherent_h1_twist_zero {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsNoetherian X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    (L : X.Modules) [isInvertibleObject L]
    (hH1 : ∀ (F : Modules X) [F.IsCoherent],
      ∃ n : ℕ, 0 < n ∧ IsZero (cohomology X (F ⊗ Modules.tensorPowerInt L n) 1))
    {T : Over S} (e : X ≅ ofOver T) :
    Scheme.Modules.isAmpleObject (Modules.toSchemeModule e L) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
