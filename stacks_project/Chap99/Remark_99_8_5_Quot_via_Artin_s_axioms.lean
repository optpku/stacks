/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap98.Remark_98_27_2_GRingStalks
public import stacks_project.Chap99.«99_8_1_1_Functor»
public import stacks_project.Chap99.Proposition_99_8_4_Representable

/-!
# Remark 99.8.5 (Quot via Artin's axioms)

If `S` is a Noetherian scheme with G-ring local rings, `f : X ⟶ S` is a
finitely presented separated morphism of algebraic spaces, and `F` is a
finitely presented quasi-coherent sheaf on `X` flat over `S`, then
`Quot_{F/X/S}` is an algebraic space locally of finite presentation over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

/-- Remark 99.8.5 (Quot via Artin's axioms): if `S` is a Noetherian scheme whose
local rings are G-rings, `f : X ⟶ ofOver (Over.mk (𝟙 S))` is a finitely
presented separated morphism of algebraic spaces, and `F` is a finitely
presented quasi-coherent module on `X` flat over `S`, then `Quot.quot f F` is
an algebraic space locally of finite presentation over `S`. This is the
Artin-axioms route to `IsLocallyOfFinitePresentationOver (quot f F)`, avoiding
algebraicity of `Coh_{X/S}` from Proposition 99.8.4. -/
@[stacks 0CZW]
theorem isLocallyOfFinitePresentationOver_of_artinAxioms
    {S : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S] [HasGRingStalks S]
    {X : AlgebraicSpace S} (f : X ⟶ ofOver (Over.mk (𝟙 S)))
    [FinitePresentation f] [Separated f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation]
    (hF_flat : Modules.flatOver F f) :
    IsLocallyOfFinitePresentationOver (quot f F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
