module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import stacks_project.Chap66.Definition_66_9_2_Dimension
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap69.«69_3_0_1_HigherDirectImage»
public import stacks_project.Chap69.Definition_69_12_1_Instances
public import stacks_project.Chap69.Lemma_69_22_7_Neighbourhood

/-!
# Vanishing of geometric stalks of higher direct images above fibre dimension

For a proper morphism of algebraic spaces with locally Noetherian target, the geometric
stalk of `R^p f_* F` at `ȳ` vanishes in degrees strictly larger than `dim(X_ȳ)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.FormalFunctions
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace
namespace FormalFunctions

/-- Lemma 69.22.9: let `S` be a scheme, let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`, and let `ȳ` be a geometric point of `Y`. Assume `Y` locally
Noetherian, `f` proper, and `dim(X_ȳ) = d`, where the geometric fibre is
`X_ȳ = fiber f ȳ = space f ȳ 1 = Spec(κ(ȳ)) ×_Y X`. Then for every coherent
`𝒪_X`-module `F` and every `p > d`, the geometric stalk `(R^p f_* F)_ȳ` is zero. -/
@[stacks 0A4T]
theorem stalkModuleCat_isZero_of_proper_of_fiberDimension_eq
    (f : X ⟶ Y) [Proper f] [IsLocallyNoetherian Y]
    [Abelian X.Modules] [Abelian Y.Modules] [HasInjectiveResolutions X.Modules]
    (ybar : GeometricPoint Y) (d : ℕ)
    (hdim : dimension (fiber f ybar) = (d : WithBot ℕ∞))
    (F : X.Modules) [F.IsCoherent] {p : ℕ} (hp : d < p) :
    IsZero (stalkModuleCat ybar (higherDirectImage f F p)) :=
  sorry

/-- If `f` is proper, `Y` is locally Noetherian, and `dim(X_ȳ) < p`, then the geometric
stalk of `R^p f_* F` at `ȳ` vanishes for every coherent `𝒪_X`-module `F`. -/
theorem stalkModuleCat_isZero_of_lt_fiberDimension
    (f : X ⟶ Y) [Proper f] [IsLocallyNoetherian Y]
    [Abelian X.Modules] [Abelian Y.Modules] [HasInjectiveResolutions X.Modules]
    (ybar : GeometricPoint Y) (F : X.Modules) [F.IsCoherent]
    {p : ℕ} (hp : dimension (fiber f ybar) < p) :
    IsZero (stalkModuleCat ybar (higherDirectImage f F p)) :=
  sorry

end FormalFunctions
end AlgebraicGeometry.AlgebraicSpace
