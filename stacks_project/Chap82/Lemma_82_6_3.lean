module

public import stacks_project.Chap69.Lemma_69_12_2_Coherent
public import stacks_project.Chap69.Lemma_69_12_8_ClosedImmersion
public import stacks_project.Chap82.Definition_82_6_1_AssociatedCycle
public import stacks_project.Chap82.Lemma_82_6_3_AssociatedCycle

/-!
# Cycle of a closed subspace as a module cycle

In the good setup of Situation 82.2.1, the `k`-cycle of a closed subspace `Y ⊂ X`
equals the `k`-cycle of the pushforward `i_* 𝒪_Y` along the closed-immersion
inclusion `i = Y.ι`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The inclusion of a closed subspace is a closed immersion. -/
instance ClosedSubspace.instIsClosedImmersion {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Y : ClosedSubspace X) : IsClosedImmersion Y.ι :=
  Y.isClosedImmersion

/-- The pushforward `i_* 𝒪_Y` of the structure module along a closed immersion is
a coherent `𝒪_X`-module on a locally Noetherian algebraic space. -/
instance instIsCoherent_pushforward_unit {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (Y : ClosedSubspace X) :
    ((pushforward Y.ι).obj
        (SheafOfModules.unit (structureSheaf Y.X) : Y.X.Modules)).IsCoherent :=
  inferInstance

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- The `δ`-dimension of the support of `i_* 𝒪_Y` is at most `k` whenever
`dim_δ(Y) ≤ k`. -/
theorem moduleSupportDeltaDimension_pushforward_unit_le
    {S : Scheme.{u}} {B X : AlgebraicSpace S} [UniversallyCatenary B]
    [IsQuasiSeparated B] (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    [IsLocallyNoetherian X] (δ : Points B → ℤ) [IsDimensionFunction δ]
    (Y : ClosedSubspace X) (k : ℤ)
    (hY : (closedSubspaceDeltaDimension f) δ Y ≤ (k : EInt)) :
    (moduleSupportDeltaDimension f) δ
        ((pushforward Y.ι).obj (SheafOfModules.unit (structureSheaf Y.X))) ≤
      (k : EInt) :=
  sorry

/-- Lemma 82.6.3: In Situation 82.2.1, let `X / B` be good. Let `Y ⊂ X` be a closed
subspace. If `dim_δ(Y) ≤ k`, then `[Y]_k = [i_* 𝒪_Y]_k` where `i : Y ⟶ X` is the
inclusion morphism `Y.ι`. -/
@[stacks 0EED]
theorem closedSubspaceCycle_eq_moduleCycle_pushforward_unit
    {S : Scheme.{u}} {B X : AlgebraicSpace S} [UniversallyCatenary B]
    [IsQuasiSeparated B] (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    [IsLocallyNoetherian X] (δ : Points B → ℤ) [IsDimensionFunction δ]
    (Y : ClosedSubspace X) (k : ℤ)
    (hY : (closedSubspaceDeltaDimension f) δ Y ≤ (k : EInt)) :
    ClosedSubspace.cycle Y ((relativeDimensionFunction f) δ) k =
      moduleCycle f δ
        ((pushforward Y.ι).obj (SheafOfModules.unit (structureSheaf Y.X))) k
        (moduleSupportDeltaDimension_pushforward_unit_le f δ Y k hY) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
