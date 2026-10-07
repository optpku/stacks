module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import stacks_project.Chap56.Lemma_56_7_5_Functor
public import stacks_project.Chap56.Lemma_56_7_5_Kernel

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
variable (x : X ⟶ Spec (CommRingCat.of k)) (y : Y ⟶ Spec (CommRingCat.of k))
variable [x.FiniteType] [y.FiniteType] [IsSeparated x]
variable [IsNoetherian X]
variable [QuasiCompact (Limits.pullback.snd x y)]
variable [QuasiSeparated (Limits.pullback.snd x y)]

/-- Lemma 56.7.5: if `k` is a field and `X`, `Y` are finite-type schemes over `k`
with `X` separated, sending a coherent kernel `K` on `Limits.pullback x y` that
is flat over `X` and has support finite over `Y` to the restriction of the
Fourier--Mukai functor (56.5.1.1) to `RingedSpace.Coh X.toRingedSpace` is an
equivalence between the full subcategory of such kernels and the category of
`k`-linear exact functors `RingedSpace.Coh X.toRingedSpace ⥤
RingedSpace.Coh Y.toRingedSpace`. -/
@[stacks 0FZN]
theorem coherentExactFourierMukai_isEquivalence :
    (coherentExactFourierMukai x y).IsEquivalence := sorry

end AlgebraicGeometry.Scheme
