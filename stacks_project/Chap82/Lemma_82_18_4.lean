module

public import stacks_project.Chap65.Lemma_65_12_2
public import stacks_project.Chap67.Lemma_67_23_5
public import stacks_project.Chap71.Definition_71_7_6_ZeroScheme
public import stacks_project.Chap82.Lemma_82_18_2_Tensor
public import stacks_project.Chap82.Lemma_82_6_3_AssociatedCycle

/-!
# Geometric first-Chern cap of a closed subspace

On a good algebraic space, intersecting the associated cycle of a closed
subspace of `δ`-dimension at most `k + 1` with `c1(L)` is the Chow class of
the associated cycle of the zero scheme of a regular section of `L` restricted
to that subspace.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ClosedSubspace

/-- The closed subspace `Z(s) ⊂ X` obtained by viewing the zero scheme of a
section of `L|_Y` as a closed subspace of `X` via `Y ⊂ X`. -/
noncomputable def zeroSchemeRestrict {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Y : ClosedSubspace X) (L : X.Modules) [isInvertibleObject L]
    (s : ((Modules.pullback Y.ι).obj L).sections) : ClosedSubspace X :=
  let Lrestrict := (Modules.pullback Y.ι).obj L
  let i := @zeroSchemeι S Y.X Lrestrict (Modules.isInvertibleObject_pullback Y.ι L) s
  @ofι S X (@zeroScheme S Y.X Lrestrict (Modules.isInvertibleObject_pullback Y.ι L) s).X
    (i ≫ Y.ι)
    (@IsClosedImmersion.comp S
      (@zeroScheme S Y.X Lrestrict (Modules.isInvertibleObject_pullback Y.ι L) s).X
      Y.X X i Y.ι
      (@zeroScheme S Y.X Lrestrict (Modules.isInvertibleObject_pullback Y.ι L) s).isClosedImmersion
      Y.isClosedImmersion)

/-- The inclusion of `zeroSchemeRestrict Y L s` is the composite of the zero
scheme of `s` on `Y` with the inclusion of `Y`. -/
theorem zeroSchemeRestrict_ι {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Y : ClosedSubspace X) (L : X.Modules) [isInvertibleObject L]
    (s : ((Modules.pullback Y.ι).obj L).sections) :
    (zeroSchemeRestrict Y L s).ι =
      (@zeroSchemeι S Y.X ((Modules.pullback Y.ι).obj L)
          (Modules.isInvertibleObject_pullback Y.ι L) s) ≫ Y.ι :=
  sorry

end ClosedSubspace

namespace Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]

/-- The associated degree-`k` cycle of a closed subspace is a `k`-cycle. -/
theorem closedSubspace_cycle_mem_cycleGroup (Y : ClosedSubspace X) (k : ℤ) :
    @ClosedSubspace.cycle S X (LocallyOfFiniteType.isLocallyNoetherian f) Y
        (relativeDimensionFunction f δ) k ∈ cycleGroup f δ k :=
  sorry

/-- The associated degree-`k` cycle of `Z(s) ⊂ X` is a `k`-cycle. -/
theorem zeroSchemeRestrict_cycle_mem_cycleGroup (L : X.Modules)
    [isInvertibleObject L] (Y : ClosedSubspace X)
    (s : ((Modules.pullback Y.ι).obj L).sections) (k : ℤ) :
    @ClosedSubspace.cycle S X (LocallyOfFiniteType.isLocallyNoetherian f)
        (ClosedSubspace.zeroSchemeRestrict Y L s) (relativeDimensionFunction f δ) k ∈
      cycleGroup f δ k :=
  sorry

/-- Lemma 82.18.4: In Situation 82.2.1 let `X / B` be good. Let `L` be an
invertible `𝒪_X`-module. Let `Y ⊂ X` be a closed subspace with
`dim_δ(Y) ≤ k + 1` and let `s` be a regular section of `L|_Y`. Then
`c1(L) ∩ [Y]_{k+1} = [Z(s)]_k` in `CH_k(X)`. -/
@[stacks 0EQN]
theorem firstChernClassCap_closedSubspace_eq_zeroSchemeCycle
    (L : X.Modules) [isInvertibleObject L] (Y : ClosedSubspace X)
    (s : ((Modules.pullback Y.ι).obj L).sections)
    [IsRegularSection ((Modules.pullback Y.ι).obj L) s] (k : ℤ)
    (hY : closedSubspaceDeltaDimension f δ Y ≤ ((k + 1 : ℤ) : EInt)) :
    firstChernClassCap f δ L k
        ⟨@ClosedSubspace.cycle S X (LocallyOfFiniteType.isLocallyNoetherian f) Y
            (relativeDimensionFunction f δ) (k + 1),
          closedSubspace_cycle_mem_cycleGroup f δ Y (k + 1)⟩ =
      chowMk f δ k
        ⟨@ClosedSubspace.cycle S X (LocallyOfFiniteType.isLocallyNoetherian f)
            (ClosedSubspace.zeroSchemeRestrict Y L s) (relativeDimensionFunction f δ) k,
          zeroSchemeRestrict_cycle_mem_cycleGroup f δ L Y s k⟩ :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
