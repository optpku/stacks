/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Topology.Sheaves.Abelian
public import ReasLib.Topology.OpenCover.Refinement
public import ReasLib.Topology.Presheaf.Cech.TermIso
public import ReasLib.Topology.Sheaf.Cohomology.Cech.ColimitComparison

/-!
# Čech connecting map in degree zero

A short exact sequence of abelian sheaves on a topological space induces an explicit boundary
map from global sections of the quotient to global Čech cohomology in degree one of the kernel.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace TopCat.Sheaf.Cohomology.Cech

variable {X : TopCat.{u}}

/-- A choice of open cover together with local `F₂`-lifts of a global section of `F₃`. -/
structure Lift {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
    (τ : S.X₃.presheaf.obj (op ⊤)) where
  /-- The open cover on which local lifts exist. -/
  cover : OpenCover.{u} X
  /-- The local `F₂`-section over each member of the cover. -/
  localSection : ∀ i : cover.index, S.X₂.presheaf.obj (op (cover.obj i))
  /-- Each local section maps to the restriction of the global `F₃`-section. -/
  isLift : ∀ i : cover.index,
    S.g.hom.app (op (cover.obj i)) (localSection i) =
      S.X₃.presheaf.map (homOfLE (le_top : cover.obj i ≤ ⊤)).op τ

/-- Package an indexed family of local `F₂`-lifts on a given open cover. -/
def Lift.ofFamily {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
    {τ : S.X₃.presheaf.obj (op ⊤)} (𝒰 : OpenCover.{u} X)
    (s : ∀ i : 𝒰.index, S.X₂.presheaf.obj (op (𝒰.obj i)))
    (hs : ∀ i : 𝒰.index,
      S.g.hom.app (op (𝒰.obj i)) (s i) =
        S.X₃.presheaf.map (homOfLE (le_top : 𝒰.obj i ≤ ⊤)).op τ) :
    Lift τ where
  cover := 𝒰
  localSection := s
  isLift := hs

/-- The cover packaged by `Lift.ofFamily` is the supplied open cover. -/
theorem Lift.ofFamily_cover {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
    {τ : S.X₃.presheaf.obj (op ⊤)} (𝒰 : OpenCover.{u} X)
    (s : ∀ i : 𝒰.index, S.X₂.presheaf.obj (op (𝒰.obj i)))
    (hs : ∀ i : 𝒰.index,
      S.g.hom.app (op (𝒰.obj i)) (s i) =
        S.X₃.presheaf.map (homOfLE (le_top : 𝒰.obj i ≤ ⊤)).op τ) :
    (Lift.ofFamily 𝒰 s hs).cover = 𝒰 := sorry

/-- A lifting cover covers the ambient space and all its local sections lift the restricted
global section. -/
theorem Lift.spec {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
    {τ : S.X₃.presheaf.obj (op ⊤)} (L : Lift τ) :
    IsOpenCover L.cover.obj ∧ ∀ i : L.cover.index,
      S.g.hom.app (op (L.cover.obj i)) (L.localSection i) =
        S.X₃.presheaf.map (homOfLE (le_top : L.cover.obj i ≤ ⊤)).op τ := sorry

/-- Opens on which a local `F₂`-lift of a global `F₃`-section exists. -/
def Lift.Index {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
    (τ : S.X₃.presheaf.obj (op ⊤)) : Type u :=
  { V : Opens X // ∃ t : S.X₂.presheaf.obj (op V),
      S.g.hom.app (op V) t =
        S.X₃.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op τ }

/-- Local surjectivity of a sheaf epimorphism makes the lift opens an open cover. -/
theorem Lift.index_isCover {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
    (hS : S.ShortExact) (τ : S.X₃.presheaf.obj (op ⊤)) :
    IsOpenCover fun V : Lift.Index τ ↦ V.val := sorry

/-- The local-surjectivity cover of a global `F₃`-section, with chosen `F₂`-lifts. -/
def Lift.ofGlobalSection {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
    (hS : S.ShortExact) (τ : S.X₃.presheaf.obj (op ⊤)) : Lift τ :=
  Lift.ofFamily (OpenCover.ofFamily (fun V : Lift.Index τ ↦ V.val)
      (Lift.index_isCover hS τ))
    (fun V ↦ Classical.choose V.property)
    (fun V ↦ Classical.choose_spec V.property)

/-- The local-surjectivity lift is indexed by the opens admitting a local `F₂`-section. -/
theorem Lift.ofGlobalSection_index {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
    (hS : S.ShortExact) (τ : S.X₃.presheaf.obj (op ⊤)) :
    (Lift.ofGlobalSection hS τ).cover.index = Lift.Index τ := sorry

/-- The `F₂`-valued Čech 1-cochain given by differences of restricted local lifts. -/
def coboundary {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
    {τ : S.X₃.presheaf.obj (op ⊤)} (L : Lift τ) :
    TopCat.Presheaf.Cech.term L.cover.obj S.X₂.presheaf 1 :=
  fun σ ↦
    S.X₂.presheaf.map
        (homOfLE (iInf_le (fun a ↦ L.cover.obj (σ a)) 0)).op (L.localSection (σ 0)) -
      S.X₂.presheaf.map
        (homOfLE (iInf_le (fun a ↦ L.cover.obj (σ a)) 1)).op (L.localSection (σ 1))

/-- Evaluating the difference cochain recovers the restricted local lifts. -/
theorem coboundary_apply {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
    {τ : S.X₃.presheaf.obj (op ⊤)} (L : Lift τ)
    (σ : Fin 2 → L.cover.index) :
    coboundary L σ =
      S.X₂.presheaf.map
          (homOfLE (iInf_le (fun a ↦ L.cover.obj (σ a)) 0)).op (L.localSection (σ 0)) -
        S.X₂.presheaf.map
          (homOfLE (iInf_le (fun a ↦ L.cover.obj (σ a)) 1)).op (L.localSection (σ 1)) := sorry

/-- The difference cochain is a Čech coboundary, represented by the negative local-lift
zero-cochain for the alternating differential. -/
theorem coboundary_eq_d {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
    {τ : S.X₃.presheaf.obj (op ⊤)} (L : Lift τ) :
    ∃ s : TopCat.Presheaf.Cech.term L.cover.obj S.X₂.presheaf 0,
      coboundary L = TopCat.Presheaf.Cech.differential L.cover.obj S.X₂.presheaf 0 s := sorry

/-- A total inverse-based `F₁`-valued cochain associated to the difference cochain. Under
short exactness it is the unique cochain mapped by `S.f` to that difference. -/
def cochain {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
    {τ : S.X₃.presheaf.obj (op ⊤)} (L : Lift τ) :
    TopCat.Presheaf.Cech.term L.cover.obj S.X₁.presheaf 1 :=
  fun σ ↦ Function.invFun (fun t ↦ S.f.hom.app
      (op (TopCat.Presheaf.Cech.intersection L.cover.obj σ)) t)
    (coboundary L σ)

/-- Under short exactness, the `F₁`-valued cochain maps to the difference cochain. -/
theorem cochain_apply {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
    (hS : S.ShortExact) {τ : S.X₃.presheaf.obj (op ⊤)} (L : Lift τ)
    (σ : Fin 2 → L.cover.index) :
    S.f.hom.app (op (TopCat.Presheaf.Cech.intersection L.cover.obj σ)) (cochain L σ) =
      coboundary L σ := sorry

/-- Under short exactness, the transported `F₁`-valued difference cochain is a cocycle in the
ordinary Čech complex. -/
theorem cochain_isCocycle {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
    (hS : S.ShortExact) {τ : S.X₃.presheaf.obj (op ⊤)} (L : Lift τ) :
    let K := TopCat.Presheaf.cechComplex L.cover.obj S.X₁.presheaf
    K.d 1 2 ((TopCat.Presheaf.Cech.termIso L.cover.obj S.X₁.presheaf 1).inv
      (cochain L)) = 0 := sorry

/-- A total inverse-based coverwise class obtained by projecting a chosen preimage under the
cycle inclusion. When the transported cochain is a cycle, it represents that cochain's class. -/
def coverwiseClass {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
    {τ : S.X₃.presheaf.obj (op ⊤)} (L : Lift τ) :
    (TopCat.Presheaf.cechComplex L.cover.obj S.X₁.presheaf).homology 1 :=
  let K := TopCat.Presheaf.cechComplex L.cover.obj S.X₁.presheaf
  K.homologyπ 1
    (Function.invFun (fun z ↦ K.iCycles 1 z)
      ((TopCat.Presheaf.Cech.termIso L.cover.obj S.X₁.presheaf 1).inv (cochain L)))

/-- Every cycle representing the transported `F₁`-cochain has the prescribed coverwise class
as its image under the homology projection. -/
theorem coverwiseClass_spec {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
    {τ : S.X₃.presheaf.obj (op ⊤)} (L : Lift τ) :
    let K := TopCat.Presheaf.cechComplex L.cover.obj S.X₁.presheaf
    ∀ z : K.cycles 1,
      K.iCycles 1 z = (TopCat.Presheaf.Cech.termIso L.cover.obj S.X₁.presheaf 1).inv
        (cochain L) → coverwiseClass L = K.homologyπ 1 z := sorry

/-- Global Čech class of a lifting cover, obtained by pushing the coverwise class along
`stageMap`. -/
def classOf {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
    {τ : S.X₃.presheaf.obj (op ⊤)} (L : Lift τ) :
    cohomology.{u, u, u} S.X₁ 1 :=
  stageMap.{u, u, u} L.cover S.X₁ 1 (ULift.up (coverwiseClass L))

/-- The global class is the image of the coverwise class under the refinement-stage map. -/
theorem classOf_spec {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
    {τ : S.X₃.presheaf.obj (op ⊤)} (L : Lift τ) :
    classOf L = stageMap.{u, u, u} L.cover S.X₁ 1 (ULift.up (coverwiseClass L)) := sorry

/-- Underlying function of the Čech boundary map on global sections. -/
def deltaToFun {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
    (hS : S.ShortExact) (τ : S.X₃.presheaf.obj (op ⊤)) :
    cohomology.{u, u, u} S.X₁ 1 :=
  classOf (Lift.ofGlobalSection hS τ)

/-- The boundary function is independent of the chosen lifting cover. -/
theorem delta_spec {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
    (hS : S.ShortExact) (τ : S.X₃.presheaf.obj (op ⊤)) (L : Lift τ) :
    deltaToFun hS τ = classOf L := sorry

/-- Additivity of the underlying Čech boundary function. -/
theorem deltaToFun_map_add {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
    (hS : S.ShortExact) (τ₁ τ₂ : S.X₃.presheaf.obj (op ⊤)) :
    deltaToFun hS (τ₁ + τ₂) = deltaToFun hS τ₁ + deltaToFun hS τ₂ := sorry

/-- The Čech boundary map `H⁰(X, F₃) ⟶ Čech H¹(X, F₁)` attached to a short exact sequence
of abelian sheaves. -/
def delta {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})} (hS : S.ShortExact) :
    (TopCat.Presheaf.Cech.Colimit.universeLift.{u}).obj (S.X₃.presheaf.obj (op ⊤)) ⟶
      cohomology.{u, u, u} S.X₁ 1 :=
  AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (fun τ ↦ deltaToFun hS (ULift.down τ))
      (fun τ₁ τ₂ ↦ deltaToFun_map_add hS (ULift.down τ₁) (ULift.down τ₂)))

/-- Evaluating the boundary morphism on a universe-lifted global section recovers `deltaToFun`. -/
theorem delta_apply {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
    (hS : S.ShortExact) (τ : S.X₃.presheaf.obj (op ⊤)) :
    delta hS (ULift.up τ) = deltaToFun hS τ := sorry

/-- Sheaf epimorphisms admit local lifts of every global section. -/
theorem exists_lift {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
    (hS : S.ShortExact) (τ : S.X₃.presheaf.obj (op ⊤)) :
    Nonempty (Lift τ) := sorry

end TopCat.Sheaf.Cohomology.Cech

end
