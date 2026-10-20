module

public import stacks_project.Chap96.Lemma_96_11_3_Pullback
public import stacks_project.Chap96.Lemma_96_11_2
public import stacks_project.Chap96.Definition_96_11_1_QCoh
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Sheafification
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open AlgebraicGeometry.GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} (X : GroupoidsOver S)

/-- Lemma 96.11.3: let `p : 𝒳 ⟶ (Sch/S)_fppf` be a category fibred in groupoids.
Let `F` be a sheaf of `𝒪_𝒳`-modules. Then `F` is quasi-coherent if and only if
`x^* F` is a quasi-coherent sheaf on `(Sch/U)_fppf` for every object `x` of `𝒳`
with `U = p(x)`. -/
@[stacks 06WI]
theorem isQuasicoherent_iff_objectPullback
    (F : SheafOfModules.{u} (structureSheaf X)) :
    F.IsQuasicoherent ↔
      ∀ x : X.total, ((objectPullback X x).obj F).IsQuasicoherent :=
  sorry

/-- Pullback of a quasi-coherent `𝒪_X`-module to `(Sch/U)_fppf` remains
quasi-coherent. -/
instance objectPullback_isQuasicoherent
    (F : SheafOfModules.{u} (structureSheaf X))
    [F.IsQuasicoherent] (x : X.total) :
    ((objectPullback X x).obj F).IsQuasicoherent :=
  sorry

/-- If every object pullback `x^* F` is quasi-coherent on `(Sch/U)_fppf`, then
`F` is quasi-coherent. -/
theorem isQuasicoherent_of_objectPullback
    (F : SheafOfModules.{u} (structureSheaf X))
    (h : ∀ x : X.total, ((objectPullback X x).obj F).IsQuasicoherent) :
    F.IsQuasicoherent :=
  sorry

end AlgebraicGeometry.GroupoidsOver
