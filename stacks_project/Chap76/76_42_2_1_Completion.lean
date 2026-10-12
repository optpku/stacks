/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Subobject.Limits
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap76.«76_42_2_1_Category»

/-!
# Completion of coherent modules on algebraic spaces

The completion functor sends a coherent module `F` to the inverse system of
ideal-power quotients `n ↦ F / I ^ n F`. Object and morphism data are built
from those cokernels; coherence and the formal-module axioms are recorded
separately.
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CoherentCompletion

variable {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]

/-- The module sheaf `F / I ^ n F` underlying stage `n` of coherent completion. -/
abbrev Stage (I : IdealSubobject X) (F : Coh X) (n : ℕ) : X.Modules :=
  cokernel (idealPowerProductSubobject I F.obj n).arrow

/-- Every ideal-power quotient stage of a coherent module along a quasi-coherent
ideal sheaf on a Noetherian algebraic space is coherent. -/
theorem stage_isCoherent (I : IdealSubobject X) [IsQuasiCoherent I] (F : Coh X)
    (n : ℕ) : (Stage I F n).IsCoherent := sorry

/-- Stage `n` of coherent completion, as an object of the coherent-module category. -/
def stage (I : IdealSubobject X) [IsQuasiCoherent I] (F : Coh X) (n : ℕ) : Coh X :=
  ⟨Stage I F n, stage_isCoherent I F n⟩

/-- The transition `F / I ^ (n + 1) F ⟶ F / I ^ n F` in module sheaves. -/
def step_modules (I : IdealSubobject X) (F : Coh X) (n : ℕ) :
    Stage I F (n + 1) ⟶ Stage I F n :=
  let h :=
    imageSubobject_le
      (action I (idealPowerProductSubobject I F.obj n : X.Modules) ≫
        (idealPowerProductSubobject I F.obj n).arrow)
      (action I (idealPowerProductSubobject I F.obj n : X.Modules)) rfl
  cokernel.map (idealPowerProductSubobject I F.obj (n + 1)).arrow
    (idealPowerProductSubobject I F.obj n).arrow (Subobject.ofLE _ _ h) (𝟙 F.obj)
    ((Category.comp_id _).trans (Subobject.ofLE_arrow h).symm)

/-- The transition `F / I ^ (n + 1) F ⟶ F / I ^ n F` in coherent modules. -/
def step (I : IdealSubobject X) [IsQuasiCoherent I] (F : Coh X) (n : ℕ) :
    stage I F (n + 1) ⟶ stage I F n :=
  ObjectProperty.homMk (step_modules I F n)

/-- The explicit inverse system `n ↦ F / I ^ n F` of coherent modules. -/
def system (I : IdealSubobject X) [IsQuasiCoherent I] (F : Coh X) :
    SequentialInverseSystem (Coh X) :=
  Functor.ofOpSequence (step I F)

/-- The ideal-power quotient system satisfies the coherent-formal-module conditions
along `I`. -/
theorem system_mem (I : IdealSubobject X) [IsQuasiCoherent I] (F : Coh X) :
    IsCoherentFormalModuleSystem I (system I F) := sorry

/-- The coherent formal module obtained by completing `F` along `I`. -/
def obj (I : IdealSubobject X) [IsQuasiCoherent I] (F : Coh X) :
    CoherentFormalModules X I :=
  ⟨system I F, system_mem I F⟩

/-- The image of `I ^ n F` under a module morphism lands in `I ^ n G`. -/
theorem idealPowerProduct_image_le (I : IdealSubobject X) {F G : X.Modules}
    (f : F ⟶ G) (n : ℕ) :
    imageSubobject ((idealPowerProductSubobject I F n).arrow ≫ f) ≤
      idealPowerProductSubobject I G n := sorry

/-- A morphism of modules induces a morphism of ideal-power product subobjects. -/
def idealPowerProductHom (I : IdealSubobject X) {F G : X.Modules} (f : F ⟶ G)
    (n : ℕ) :
    (idealPowerProductSubobject I F n : X.Modules) ⟶
      (idealPowerProductSubobject I G n : X.Modules) :=
  factorThruImageSubobject ((idealPowerProductSubobject I F n).arrow ≫ f) ≫
    Subobject.ofLE _ _ (idealPowerProduct_image_le I f n)

/-- The induced map on ideal-power products lies over the original module morphism. -/
theorem idealPowerProductHom_arrow (I : IdealSubobject X) {F G : X.Modules}
    (f : F ⟶ G) (n : ℕ) :
    (idealPowerProductSubobject I F n).arrow ≫ f =
      idealPowerProductHom I f n ≫ (idealPowerProductSubobject I G n).arrow := sorry

/-- A morphism of coherent modules induces a morphism of completion stages in
module sheaves. -/
def stageMap_modules (I : IdealSubobject X) {F G : Coh X} (f : F ⟶ G) (n : ℕ) :
    Stage I F n ⟶ Stage I G n :=
  cokernel.map (idealPowerProductSubobject I F.obj n).arrow
    (idealPowerProductSubobject I G.obj n).arrow
    (idealPowerProductHom I f.hom n) f.hom (idealPowerProductHom_arrow I f.hom n)

/-- A morphism of coherent modules induces a morphism on every completion stage. -/
def stageMap (I : IdealSubobject X) [IsQuasiCoherent I] {F G : Coh X} (f : F ⟶ G)
    (n : ℕ) : stage I F n ⟶ stage I G n :=
  ObjectProperty.homMk (stageMap_modules I f n)

/-- Stage maps commute with the successor transitions of coherent completion. -/
theorem stageMap_naturality (I : IdealSubobject X) [IsQuasiCoherent I]
    {F G : Coh X} (f : F ⟶ G) (n : ℕ) :
    step I F n ≫ stageMap I f n = stageMap I f (n + 1) ≫ step I G n := sorry

/-- Stage maps satisfy the successor equation in the form used by
`NatTrans.ofOpSequence`. -/
theorem systemMap_naturality (I : IdealSubobject X) [IsQuasiCoherent I]
    {F G : Coh X} (f : F ⟶ G) (n : ℕ) :
    (system I F).map (homOfLE (Nat.le_add_right n 1)).op ≫ stageMap I f n =
      stageMap I f (n + 1) ≫
        (system I G).map (homOfLE (Nat.le_add_right n 1)).op := sorry

/-- The natural transformation between ideal-power quotient systems induced by
`f`. -/
def systemMap (I : IdealSubobject X) [IsQuasiCoherent I] {F G : Coh X} (f : F ⟶ G) :
    system I F ⟶ system I G :=
  NatTrans.ofOpSequence (stageMap I f) (systemMap_naturality I f)

/-- The morphism between coherent formal completions induced by `f`. -/
def map (I : IdealSubobject X) [IsQuasiCoherent I] {F G : Coh X} (f : F ⟶ G) :
    obj I F ⟶ obj I G :=
  ObjectProperty.homMk (systemMap I f)

/-- Completion sends identity morphisms to identity morphisms. -/
theorem map_id (I : IdealSubobject X) [IsQuasiCoherent I] (F : Coh X) :
    map I (𝟙 F) = 𝟙 (obj I F) := sorry

/-- Completion sends composites to composites. -/
theorem map_comp (I : IdealSubobject X) [IsQuasiCoherent I] {F G H : Coh X}
    (f : F ⟶ G) (g : G ⟶ H) : map I (f ≫ g) = map I f ≫ map I g := sorry

/-- The canonical completion functor `Coh(𝒪_X) ⥤ Coh(X, I)`, sending `F` to the
system `n ↦ F / I ^ n F`. -/
def functor (I : IdealSubobject X) [IsQuasiCoherent I] :
    Coh X ⥤ CoherentFormalModules X I where
  obj := obj I
  map := map I
  map_id := map_id I
  map_comp := map_comp I

/-- Stage `n` of the canonical completion functor is the coherent ideal-power
quotient. -/
def stageIso (I : IdealSubobject X) [IsQuasiCoherent I] (F : Coh X) (n : ℕ) :
    stage I F n ≅ (((functor I).obj F).obj).obj (op n) :=
  Iso.refl _

/-- Stage `n` of the completion functor is the coherent wrapper of `F / I ^ n F`. -/
theorem functor_obj_eq (I : IdealSubobject X) [IsQuasiCoherent I] (F : Coh X)
    (n : ℕ) : ((((functor I).obj F).obj).obj (op n)) = stage I F n := sorry

end AlgebraicGeometry.AlgebraicSpace.CoherentCompletion
