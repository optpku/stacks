/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.FMap
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.Underlying
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections
import Mathlib.Tactic.CrossRefAttribute

/-!
# Module-linear Cech maps associated to morphisms of ringed spaces

For an `f`-map and a refinement, this file lifts the established additive Cech map to the
common coefficient category `ModuleCat (globalSectionsRing Y)`.  On the source this is the
module-valued Cech complex of `Y`; on the target it is the module-valued Cech complex of `X`
after restriction of scalars along `Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)`.

The underlying function in every degree is the existing additive map.  Thus the new data are
concrete; only its module-linearity and compatibility with the differentials are proof fields.
The generic module-valued refinement API applies to the final, same-space refinement segment.
The preceding change-of-space segment still passes through the additive pushforward/preimage
comparison, because no module-valued presheaf comparison across the two slice sites is currently
available; `underlyingMap` records that boundary explicitly.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleCech.FMap.Linear

variable {X Y : RingedSpace.{u}}

/-- The module-valued Cech complex on a cover of `Y`, with coefficients in
`ModuleCat (globalSectionsRing Y)`. -/
@[stacks 01FD "module-linear Cech f-map source"]
abbrev sourceComplex {J : Type u} (V : J → Opens Y.carrier)
    (hV : iSup V = ⊤) (G : Y.Modules) :
    CochainComplex (ModuleCat (globalSectionsRing Y)) ℕ :=
  (ModuleCech.complex (⊤ : Opens Y.carrier)
    (Opens.Cover.overFamily ⊤ V hV)).obj G

/-- The module-valued Cech complex on a cover of `X`, before changing its global scalars. -/
@[stacks 01FD "module-linear Cech f-map target before scalar restriction"]
abbrev targetComplexRaw {I : Type u} (U : I → Opens X.carrier)
    (hU : iSup U = ⊤) (F : X.Modules) :
    CochainComplex (ModuleCat (globalSectionsRing X)) ℕ :=
  (ModuleCech.complex (⊤ : Opens X.carrier)
    (Opens.Cover.overFamily ⊤ U hU)).obj F

/-- The target Cech complex over `Γ(Y, 𝒪_Y)`, obtained by restricting the scalar action on
the module-valued Cech complex of `X`. -/
@[stacks 01FD "module-linear Cech f-map target"]
abbrev targetComplex (f : X ⟶ Y) {I : Type u} (U : I → Opens X.carrier)
    (hU : iSup U = ⊤) (F : X.Modules) :
    CochainComplex (ModuleCat (globalSectionsRing Y)) ℕ :=
  ((moduleSectionsRestrictionFunctor f ⊤).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (targetComplexRaw U hU F)

/-- The additive map underlying the module-linear Cech `f`-map.  It is obtained by identifying
the forgotten module-valued complexes with the established additive Cech complexes and then
applying `FMap.complexMap`. -/
@[stacks 01FD "underlying additive map of the module-linear Cech f-map"]
noncomputable abbrev underlyingMap
    (f : X ⟶ Y) {I J : Type u}
    (U : I → Opens X.carrier) (hU : iSup U = ⊤)
    (V : J → Opens Y.carrier) (hV : iSup V = ⊤)
    (c : I → J) (hc : IsRefinement (fun j ↦ preimageOpen f (V j)) U c)
    {G : Y.Modules} {F : X.Modules}
    (φ : G ⟶ (RingedSpace.Hom.pushforward f).obj F) :=
  (Underlying.complexIso (⊤ : Opens Y.carrier) V hV).hom.app G ≫
    FMap.complexMap f U V c hc φ ≫
    (Underlying.complexIso (⊤ : Opens X.carrier) U hU).inv.app F

/-- The underlying function of the degree-`n` module-linear Cech component. -/
@[stacks 01FD "underlying function of a module-linear Cech component"]
noncomputable abbrev componentFn
    (f : X ⟶ Y) {I J : Type u}
    (U : I → Opens X.carrier) (hU : iSup U = ⊤)
    (V : J → Opens Y.carrier) (hV : iSup V = ⊤)
    (c : I → J) (hc : IsRefinement (fun j ↦ preimageOpen f (V j)) U c)
    {G : Y.Modules} {F : X.Modules}
    (φ : G ⟶ (RingedSpace.Hom.pushforward f).obj F) (n : ℕ) :
    (sourceComplex V hV G).X n → (targetComplex f U hU F).X n :=
  fun x ↦ (underlyingMap f U hU V hV c hc φ).f n x

/-- The carrier map of a module-linear Cech component preserves addition. -/
@[stacks 01FD "additivity of a module-linear Cech component"]
theorem componentFn_add
    (f : X ⟶ Y) {I J : Type u}
    (U : I → Opens X.carrier) (hU : iSup U = ⊤)
    (V : J → Opens Y.carrier) (hV : iSup V = ⊤)
    (c : I → J) (hc : IsRefinement (fun j ↦ preimageOpen f (V j)) U c)
    {G : Y.Modules} {F : X.Modules}
    (φ : G ⟶ (RingedSpace.Hom.pushforward f).obj F) (n : ℕ)
    (x y : (sourceComplex V hV G).X n) :
    componentFn f U hU V hV c hc φ n (x + y) =
      componentFn f U hU V hV c hc φ n x +
        componentFn f U hU V hV c hc φ n y := sorry

/-- The carrier map of a module-linear Cech component respects the
`Γ(Y, 𝒪_Y)`-scalar action. -/
@[stacks 01FD "linearity of a module-linear Cech component"]
theorem componentFn_smul
    (f : X ⟶ Y) {I J : Type u}
    (U : I → Opens X.carrier) (hU : iSup U = ⊤)
    (V : J → Opens Y.carrier) (hV : iSup V = ⊤)
    (c : I → J) (hc : IsRefinement (fun j ↦ preimageOpen f (V j)) U c)
    {G : Y.Modules} {F : X.Modules}
    (φ : G ⟶ (RingedSpace.Hom.pushforward f).obj F) (n : ℕ)
    (r : globalSectionsRing Y) (x : (sourceComplex V hV G).X n) :
    componentFn f U hU V hV c hc φ n (r • x) =
      r • componentFn f U hU V hV c hc φ n x := sorry

/-- The degree-`n` component of the Cech `f`-map, equipped with its
`Γ(Y, 𝒪_Y)`-linear structure. -/
@[stacks 01FD "component of the module-linear Cech f-map"]
noncomputable def component
    (f : X ⟶ Y) {I J : Type u}
    (U : I → Opens X.carrier) (hU : iSup U = ⊤)
    (V : J → Opens Y.carrier) (hV : iSup V = ⊤)
    (c : I → J) (hc : IsRefinement (fun j ↦ preimageOpen f (V j)) U c)
    {G : Y.Modules} {F : X.Modules}
    (φ : G ⟶ (RingedSpace.Hom.pushforward f).obj F) (n : ℕ) :
    (sourceComplex V hV G).X n ⟶ (targetComplex f U hU F).X n :=
  @ModuleCat.ofHom (globalSectionsRing Y) _
    ((sourceComplex V hV G).X n) ((targetComplex f U hU F).X n)
    (ModuleCat.isAddCommGroup ((sourceComplex V hV G).X n))
    (ModuleCat.isModule ((sourceComplex V hV G).X n))
    (ModuleCat.isAddCommGroup ((targetComplex f U hU F).X n))
    (ModuleCat.isModule ((targetComplex f U hU F).X n))
    { toFun := componentFn f U hU V hV c hc φ n
      map_add' := componentFn_add f U hU V hV c hc φ n
      map_smul' := componentFn_smul f U hU V hV c hc φ n }

/-- The module-linear Cech components commute with the Cech differentials. -/
@[stacks 01FD "differential compatibility of the module-linear Cech f-map"]
theorem component_comm
    (f : X ⟶ Y) {I J : Type u}
    (U : I → Opens X.carrier) (hU : iSup U = ⊤)
    (V : J → Opens Y.carrier) (hV : iSup V = ⊤)
    (c : I → J) (hc : IsRefinement (fun j ↦ preimageOpen f (V j)) U c)
    {G : Y.Modules} {F : X.Modules}
    (φ : G ⟶ (RingedSpace.Hom.pushforward f).obj F) (i j : ℕ)
    (hij : (ComplexShape.up ℕ).Rel i j) :
    component f U hU V hV c hc φ i ≫ (targetComplex f U hU F).d i j =
      (sourceComplex V hV G).d i j ≫ component f U hU V hV c hc φ j := sorry

/-- The concrete `Γ(Y, 𝒪_Y)`-linear cochain map induced by an `f`-map and a refinement. -/
@[stacks 01FD "module-linear Cech complex map of an f-map and refinement"]
noncomputable def complexMap
    (f : X ⟶ Y) {I J : Type u}
    (U : I → Opens X.carrier) (hU : iSup U = ⊤)
    (V : J → Opens Y.carrier) (hV : iSup V = ⊤)
    (c : I → J) (hc : IsRefinement (fun j ↦ preimageOpen f (V j)) U c)
    {G : Y.Modules} {F : X.Modules}
    (φ : G ⟶ (RingedSpace.Hom.pushforward f).obj F) :
    sourceComplex V hV G ⟶ targetComplex f U hU F where
  f n := component f U hU V hV c hc φ n
  comm' i j hij := component_comm f U hU V hV c hc φ i j hij

/-- In each degree, forgetting scalar structure from `complexMap` recovers `underlyingMap`. -/
@[stacks 01FD "underlying component of the module-linear Cech f-map"]
theorem complexMap_forget_f
    (f : X ⟶ Y) {I J : Type u}
    (U : I → Opens X.carrier) (hU : iSup U = ⊤)
    (V : J → Opens Y.carrier) (hV : iSup V = ⊤)
    (c : I → J) (hc : IsRefinement (fun j ↦ preimageOpen f (V j)) U c)
    {G : Y.Modules} {F : X.Modules}
    (φ : G ⟶ (RingedSpace.Hom.pushforward f).obj F) (n : ℕ) :
    ((forget₂ (ModuleCat (globalSectionsRing Y)) AddCommGrpCat).map
      ((complexMap f U hU V hV c hc φ).f n)).hom =
        ((underlyingMap f U hU V hV c hc φ).f n).hom := sorry

/-- The bounded-below derived source of the module-linear Cech `f`-map. -/
@[stacks 01FD "bounded-below module-linear Cech f-map source"]
abbrev derivedSource {J : Type u} (V : J → Opens Y.carrier)
    (hV : iSup V = ⊤) (G : Y.Modules) :
    DerivedCategory.Plus (ModuleCat (globalSectionsRing Y)) :=
  (DerivedCategory.Plus.Q :
    CochainComplex.Plus (ModuleCat (globalSectionsRing Y)) ⥤
      DerivedCategory.Plus (ModuleCat (globalSectionsRing Y))).obj
    ((CochainComplex.Plus.extendNat (ModuleCat (globalSectionsRing Y))).obj
      (sourceComplex V hV G))

/-- The bounded-below derived target of the module-linear Cech `f`-map. -/
@[stacks 01FD "bounded-below module-linear Cech f-map target"]
abbrev derivedTarget (f : X ⟶ Y) {I : Type u} (U : I → Opens X.carrier)
    (hU : iSup U = ⊤) (F : X.Modules) :
    DerivedCategory.Plus (ModuleCat (globalSectionsRing Y)) :=
  (DerivedCategory.Plus.Q :
    CochainComplex.Plus (ModuleCat (globalSectionsRing Y)) ⥤
      DerivedCategory.Plus (ModuleCat (globalSectionsRing Y))).obj
    ((CochainComplex.Plus.extendNat (ModuleCat (globalSectionsRing Y))).obj
      (targetComplex f U hU F))

/-- Localizing the module-linear Cech map in
`DerivedCategory.Plus (ModuleCat (globalSectionsRing Y))`. -/
@[stacks 01FD "bounded-below module-linear Cech map of an f-map"]
noncomputable def derivedMap
    (f : X ⟶ Y) {I J : Type u}
    (U : I → Opens X.carrier) (hU : iSup U = ⊤)
    (V : J → Opens Y.carrier) (hV : iSup V = ⊤)
    (c : I → J) (hc : IsRefinement (fun j ↦ preimageOpen f (V j)) U c)
    {G : Y.Modules} {F : X.Modules}
    (φ : G ⟶ (RingedSpace.Hom.pushforward f).obj F) :
    derivedSource V hV G ⟶ derivedTarget f U hU F :=
  (DerivedCategory.Plus.Q :
    CochainComplex.Plus (ModuleCat (globalSectionsRing Y)) ⥤
      DerivedCategory.Plus (ModuleCat (globalSectionsRing Y))).map
    ((CochainComplex.Plus.extendNat (ModuleCat (globalSectionsRing Y))).map
      (complexMap f U hU V hV c hc φ))

/-- Degree-`p` module-valued Cech cohomology on the source cover. -/
@[stacks 01FD "module-linear Cech cohomology f-map source"]
abbrev cohomologySource {J : Type u} (V : J → Opens Y.carrier)
    (hV : iSup V = ⊤) (G : Y.Modules) (p : ℕ) :
    ModuleCat (globalSectionsRing Y) :=
  (HomologicalComplex.homologyFunctor
    (ModuleCat (globalSectionsRing Y)) (ComplexShape.up ℕ) p).obj
      (sourceComplex V hV G)

/-- Degree-`p` module-valued Cech cohomology on the target cover after scalar restriction. -/
@[stacks 01FD "module-linear Cech cohomology f-map target"]
abbrev cohomologyTarget (f : X ⟶ Y) {I : Type u}
    (U : I → Opens X.carrier) (hU : iSup U = ⊤)
    (F : X.Modules) (p : ℕ) : ModuleCat (globalSectionsRing Y) :=
  (HomologicalComplex.homologyFunctor
    (ModuleCat (globalSectionsRing Y)) (ComplexShape.up ℕ) p).obj
      (targetComplex f U hU F)

/-- The `Γ(Y, 𝒪_Y)`-linear map on Cech cohomology induced by an `f`-map and a refinement. -/
@[stacks 01FD "module-linear Cech cohomology map of an f-map"]
noncomputable def cohomologyMap
    (f : X ⟶ Y) {I J : Type u}
    (U : I → Opens X.carrier) (hU : iSup U = ⊤)
    (V : J → Opens Y.carrier) (hV : iSup V = ⊤)
    (c : I → J) (hc : IsRefinement (fun j ↦ preimageOpen f (V j)) U c)
    {G : Y.Modules} {F : X.Modules}
    (φ : G ⟶ (RingedSpace.Hom.pushforward f).obj F) (p : ℕ) :
    cohomologySource V hV G p ⟶ cohomologyTarget f U hU F p :=
  (HomologicalComplex.homologyFunctor
    (ModuleCat (globalSectionsRing Y)) (ComplexShape.up ℕ) p).map
      (complexMap f U hU V hV c hc φ)

end AlgebraicGeometry.RingedSpace.ModuleCech.FMap.Linear
