/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.ChosenPresentation.SmallToBig.Comparison
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.InducedTopology

/-!
# Sections of small-to-big pro-étale inverse images

The big inverse image of a small pro-étale sheaf evaluates as global sections
of its small inverse image and satisfies fpqc descent.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped MorphismOfTopoiIn

universe u v w

namespace AlgebraicGeometry.ChosenBigProetaleSite

open SmallToBig

/-- Sections of the big inverse image at `T ⟶ S` are canonically isomorphic
to global sections of the small inverse image on `T`. -/
noncomputable def siteMorphismInverseImage_objIso {X : ChosenBigProetaleSite.{u, v}}
    {S T : X.carrier} (f : T ⟶ S)
    [UnivLE.{max u v, w}]
    [HasWeakSheafify (bigTopology X S) (Type w)]
    [HasWeakSheafify (smallTopology X T) (Type w)]
    (F : Sheaf (smallTopology X S) (Type w)) :
    (((siteMorphismOfTopoi X S)⁻¹).obj F).1.obj (op (Over.mk f)) ≅
      (((smallMorphism f)⁻¹).obj F).1.obj (op (smallTerminalObject X T)) := by
  let G := ((siteMorphismOfTopoi X S)⁻¹).obj F
  let U := smallTerminalObject X T
  let e : (relocalizationFunctor f).obj U ≅ Over.mk f :=
    Over.isoMk (Iso.refl T) (by rfl)
  exact G.1.mapIso e.op ≪≫ (inverseImage_objObjIso f G U).symm ≪≫
    (((sheafToPresheaf (smallTopology X T) (Type w)).mapIso
      ((smallMorphism_comp_inverseImageIso f).app F)).app (op U)).symm

/-- The big inverse image of a small pro-étale sheaf satisfies the sheaf
condition for fpqc coverings on the chosen slice. -/
theorem siteMorphismInverseImage_isSheaf_fpqc {X : ChosenBigProetaleSite.{u, v}}
    (S : X.carrier) [UnivLE.{max u v, w}]
    [HasWeakSheafify (bigTopology X S) (Type w)]
    (F : Sheaf (smallTopology X S) (Type w)) :
    Presheaf.IsSheaf
      ((Over.post X.toScheme).restrictedTopology
        (Scheme.fpqcTopology.over (X.toScheme.obj S)))
      (((siteMorphismOfTopoi X S)⁻¹).obj F).1 :=
  sorry

end AlgebraicGeometry.ChosenBigProetaleSite
