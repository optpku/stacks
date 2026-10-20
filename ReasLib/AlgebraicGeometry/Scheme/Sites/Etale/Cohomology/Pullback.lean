/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.GlobalSections
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.CategoryTheory.Sites.Sheafification.FreeAbelianYoneda.Weak
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-!
# Pullback of global étale cohomology

Exact inverse image maps Ext groups. The free abelian global representable on
the target maps to the inverse image of the source generator through the unit
section, yielding pullback on global étale cohomology.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable [∀ {S T : Scheme.{u}} (f : T ⟶ S),
    ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
      S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint]

/-- Inverse image and continuous direct image of abelian small étale sheaves are adjoint. -/
def smallEtaleSheafAdjunction {S T : Scheme.{u}} (f : T ⟶ S)
    [HasWeakSheafify T.smallEtaleTopology AddCommGrpCat.{u}] :
    (smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
        S.smallEtaleTopology T.smallEtaleTopology ⊣
      (smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
        S.smallEtaleTopology T.smallEtaleTopology :=
  (smallEtalePullback f).sheafAdjunctionContinuous AddCommGrpCat.{u}
    S.smallEtaleTopology T.smallEtaleTopology

/-- Inverse image of abelian small étale sheaves is a left adjoint. -/
instance smallEtalePullbackAbelian_isLeftAdjoint {S T : Scheme.{u}} (f : T ⟶ S)
    [HasWeakSheafify T.smallEtaleTopology AddCommGrpCat.{u}] :
    ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
      S.smallEtaleTopology T.smallEtaleTopology).IsLeftAdjoint :=
  (smallEtaleSheafAdjunction f).isLeftAdjoint

/-- Inverse image of abelian small étale sheaves preserves finite limits. -/
instance smallEtalePullbackAbelian_preservesFiniteLimits {S T : Scheme.{u}} (f : T ⟶ S)
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}] :
    PreservesFiniteLimits ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
      S.smallEtaleTopology T.smallEtaleTopology) := sorry

/-- The target global free abelian representable maps to the inverse image of the source
generator by the transported adjunction-unit section of its identity morphism. -/
def generatorPullbackHom {S T : Scheme.{u}} (f : T ⟶ S)
    [HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasWeakSheafify T.smallEtaleTopology AddCommGrpCat.{u}] :
    GrothendieckTopology.FreeAbelianYoneda.obj T.smallEtaleTopology (globalEtale T) ⟶
      ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
        S.smallEtaleTopology T.smallEtaleTopology).obj
          (GrothendieckTopology.FreeAbelianYoneda.obj S.smallEtaleTopology (globalEtale S)) :=
  let generator :=
    GrothendieckTopology.FreeAbelianYoneda.obj S.smallEtaleTopology (globalEtale S)
  let pull := (smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
    S.smallEtaleTopology T.smallEtaleTopology
  let generatorSection := GrothendieckTopology.FreeAbelianYoneda.homEquiv
    S.smallEtaleTopology (globalEtale S) generator (𝟙 generator)
  let unitSection :=
    ((smallEtaleSheafAdjunction f).unit.app generator).hom.app
      (op (globalEtale S)) generatorSection
  (GrothendieckTopology.FreeAbelianYoneda.homEquiv
    T.smallEtaleTopology (globalEtale T) (pull.obj generator)).symm
      ((pull.obj generator).obj.map (op (globalEtalePullbackIso f).inv) unitSection)

/-- The section of the generator comparison is the adjunction-unit image of the source
identity section, transported along base change of the global étale object. -/
theorem generatorPullbackHom_spec {S T : Scheme.{u}} (f : T ⟶ S)
    [HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasWeakSheafify T.smallEtaleTopology AddCommGrpCat.{u}] :
    let generator :=
      GrothendieckTopology.FreeAbelianYoneda.obj S.smallEtaleTopology (globalEtale S)
    let pull := (smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
      S.smallEtaleTopology T.smallEtaleTopology
    GrothendieckTopology.FreeAbelianYoneda.homEquiv
        T.smallEtaleTopology (globalEtale T) (pull.obj generator) (generatorPullbackHom f) =
      (pull.obj generator).obj.map (op (globalEtalePullbackIso f).inv)
        (((smallEtaleSheafAdjunction f).unit.app generator).hom.app (op (globalEtale S))
          (GrothendieckTopology.FreeAbelianYoneda.homEquiv
            S.smallEtaleTopology (globalEtale S) generator (𝟙 generator))) := sorry

/-- Pullback on global étale cohomology is the exact inverse-image map on Ext followed
by precomposition with the global generator comparison. -/
def cohomologyPullback {S T : Scheme.{u}} (f : T ⟶ S)
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]
    [HasWeakSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    G.H' n (globalEtale S) ⟶
      ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
          S.smallEtaleTopology T.smallEtaleTopology).obj G |>.H' n (globalEtale T) :=
  let pull := (smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
    S.smallEtaleTopology T.smallEtaleTopology
  let generator :=
    GrothendieckTopology.FreeAbelianYoneda.obj S.smallEtaleTopology (globalEtale S)
  AddCommGrpCat.ofHom (pull.mapExtAddHom generator G n) ≫
    AddCommGrpCat.ofHom
      ((Abelian.Ext.mk₀ (generatorPullbackHom f)).precomp (pull.obj G) (zero_add n))

end AlgebraicGeometry.Scheme.Etale

namespace AlgebraicGeometry.Scheme.Hom

end AlgebraicGeometry.Scheme.Hom

end
