/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap76.Theorem_76_22_1
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.Locus.BaseChange
import StacksCheckRecall

/-!
# Openness of the relative-flatness locus after a finite-type base

If `X` is locally of finite presentation over `Z`, `Y` is locally of finite type
over `Z`, and a finitely presented module on `X` is flat over `Z`, then the
locus of points at which the module is flat over `Y` is open, and it commutes
with arbitrary base change of `Z`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/- Lemma 76.23.5 (1): Under local finite presentation of `X` over `Z`, finite
presentation and flatness of `F` over `Z`, and local finite type of `Y` over `Z`,
the relative-flatness locus of `F` over `Y` is open. -/
@[stacks 05X2] #check (AlgebraicGeometry.AlgebraicSpace.Modules.isOpen_flatOverAt_of_flatOver :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (h : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ h)]
    [LocallyOfFiniteType h] (F : X.Modules) [F.IsFinitePresentation]
    (h_flat : flatOver F (f ≫ h)), IsOpen (flatOverLocus F f))

/- Lemma 76.23.5 (2): Under the same hypotheses, the relative-flatness locus of
the pulled-back module is the inverse image of the original locus after every
base change `g : Z' ⟶ Z`. -/
@[stacks 05X2] #check (AlgebraicGeometry.AlgebraicSpace.Modules.flatOverLocus_baseChange_eq_preimage :
  ∀ {S : Scheme.{u}} {X Y Z Z' : AlgebraicSpace S}
    (f : X ⟶ Y) (h : Y ⟶ Z) (g : Z' ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ h)] [LocallyOfFiniteType h]
    (F : X.Modules) [F.IsFinitePresentation] (h_flat : flatOver F (f ≫ h)),
    flatOverLocus ((pullback (pullback.fst (f ≫ h) g)).obj F)
        (overBaseChange f h g) =
      Points.map (pullback.fst (f ≫ h) g) ⁻¹' flatOverLocus F f)

end AlgebraicGeometry.AlgebraicSpace.Modules
