/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap61.Lemma_61_12_16_Comparison
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.InducedTopology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 61.16.3

The inverse image along `π_S` is computed by global sections of the small
pro-étale inverse image, and is an fpqc sheaf on the chosen slice.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open scoped MorphismOfTopoiIn

universe u v w

namespace AlgebraicGeometry.ChosenBigProetaleSite

open SmallToBig

/-- Lemma 61.16.3 (1): for a sheaf `F` on `S_proétale` and `f : T ⟶ S`, the inverse
image along `π_S : (Sch/S)_proétale ⟶ S_proétale` evaluates at `Over.mk f` as the
global sections of `f_small⁻¹ F` on `T_proétale`. -/
@[stacks 0F65]
theorem siteMorphismInverseImage_obj {X : ChosenBigProetaleSite.{u, v}}
    {S T : X.carrier} (f : T ⟶ S)
    [HasWeakSheafify (bigTopology X S) (Type w)]
    [HasWeakSheafify (smallTopology X T) (Type w)]
    (F : Sheaf (smallTopology X S) (Type w)) :
    (((siteMorphismOfTopoi X S)⁻¹).obj F).1.obj (op (Over.mk f)) =
      (((smallMorphism f)⁻¹).obj F).1.obj (op (smallTerminalObject X T)) :=
  sorry

/-- Lemma 61.16.3 (2): for a sheaf `F` on `S_proétale`, the inverse image `π_S⁻¹ F`
satisfies the sheaf condition for fpqc coverings on the chosen slice over `S`. -/
@[stacks 0F65]
theorem siteMorphismInverseImage_isSheaf_fpqc {X : ChosenBigProetaleSite.{u, v}}
    (S : X.carrier) [HasWeakSheafify (bigTopology X S) (Type w)]
    (F : Sheaf (smallTopology X S) (Type w)) :
    Presheaf.IsSheaf
      ((Over.post X.toScheme).restrictedTopology
        (Scheme.fpqcTopology.over (X.toScheme.obj S)))
      (((siteMorphismOfTopoi X S)⁻¹).obj F).1 :=
  sorry

end AlgebraicGeometry.ChosenBigProetaleSite
