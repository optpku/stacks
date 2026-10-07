module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import stacks_project.Chap30.Lemma_30_20_7_Neighbourhood
public import stacks_project.Chap30.Lemma_30_20_7_Tower
public import stacks_project.Chap30.Lemma_30_20_7_Comparison

/-!
# Formal functions on stalks

For a proper morphism to a locally Noetherian scheme and a coherent sheaf, the
completed stalk of a higher direct image is isomorphic to the inverse limit of
cohomology of infinitesimal neighbourhoods of the fibre.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace FiberNeighbourhood

variable {X Y : Scheme.{u}}
variable [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

/-- Lemma 30.20.7: given a proper morphism `f : X ⟶ Y` with `Y` locally Noetherian
and a coherent sheaf `F` on `X`, for every point `y` of `Y` and every `p`,
the `m_y`-adic completion of the stalk `(R^p f_* F)_y` is isomorphic to
`lim_n H^p(X_n, F_n)` as `𝒪_{Y,y}^∧`-modules, where
`X_n = Spec(𝒪_{Y,y} ⧸ m_y^n) ×_Y X` is the infinitesimal neighbourhood of the
fibre `X_1 = X_y` and `F_n = i_n^* F`. Internally `scheme f y n` is the source's
`X_{n+1}`, so `n = 0` recovers `X_y`. -/
@[stacks 02OD, instance]
instance isIso_limitComparison [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsProper f]
    (F : X.Modules) [F.IsCoherent] (y : Y) (p : ℕ) :
    IsIso (limitComparison f F y p) :=
  sorry

end FiberNeighbourhood
end AlgebraicGeometry.Scheme.Hom
