/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap69.Definition_69_12_1_Instances
public import stacks_project.Chap69.Lemma_69_22_7_Comparison
public import stacks_project.Chap69.Lemma_69_22_7_Neighbourhood

/-!
# Geometric-stalk form of the theorem on formal functions

For a proper morphism of algebraic spaces with locally Noetherian target and a
coherent sheaf, the m_ȳ-adic completion of the geometric stalk of R^p f_* F is
identified with the inverse limit of neighbourhood cohomology H^p(X_n, F_n).
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.FormalFunctions
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `cohomologyOver`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace
namespace FormalFunctions

/-- Lemma 69.22.7: let `S` be a scheme, let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`, and let `F` be a quasi-coherent sheaf on `X`. Assume `Y` locally
Noetherian, `f` proper, and `F` coherent. Let `ȳ` be a geometric point of `Y`.
Writing `X_n = space f ȳ n` for the infinitesimal neighbourhood
`Spec(O_{Y,ȳ}/m_ȳ^n) ×_Y X`, with `i_n = toX f ȳ n`, `f_n = toSpec f ȳ n`,
`c_n = toY ȳ n`, and `F_n = sheaf f F ȳ n`, the comparison
`limitComparison f F ȳ p` from the `m_ȳ`-adic completion of
`(R^p f_* F)_ȳ` to `lim_n H^p(X_n, F_n)` is an isomorphism of
`O_{Y,ȳ}^∧`-modules. -/
@[stacks 08B1]
instance isIso_limitComparison [IsLocallyNoetherian Y] (f : X ⟶ Y) [Proper f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsCoherent] (ybar : GeometricPoint Y)
    [Abelian X.Modules] [Abelian Y.Modules]
    [∀ n, Abelian (space f ybar n).Modules]
    [∀ n, Abelian (thickening ybar n).Modules]
    [Abelian (spaceInf f ybar).Modules]
    [Abelian (specSpace ybar).Modules]
    [HasInjectiveResolutions X.Modules]
    [∀ n, HasInjectiveResolutions (space f ybar n).Modules]
    [HasInjectiveResolutions (spaceInf f ybar).Modules] (p : ℕ) :
    IsIso (limitComparison f F ybar p) :=
  sorry

end FormalFunctions
end AlgebraicGeometry.AlgebraicSpace
