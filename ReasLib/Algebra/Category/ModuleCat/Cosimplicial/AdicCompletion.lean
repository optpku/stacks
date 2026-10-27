/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Cosimplicial.Module
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Functoriality

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u

/-- A family of ideals compatible with the structure maps of a cosimplicial ring. -/
structure CosimplicialIdeal (A : CosimplicialObject CommRingCat.{u}) where
  /-- The ideal in each degree. -/
  obj : (n : SimplexCategory) → Ideal (A.obj n)
  /-- The structure maps carry each ideal into the ideal in the target degree. -/
  map_mem : ∀ {n m : SimplexCategory} (σ : n ⟶ m) {x : A.obj n},
    x ∈ obj n → (A.map σ).hom x ∈ obj m

namespace CosimplicialIdeal

/-- A compatible family of ideals determines a cosimplicial ideal. -/
def ofFamily {A : CosimplicialObject CommRingCat.{u}}
    (obj : (n : SimplexCategory) → Ideal (A.obj n))
    (map_mem : ∀ {n m : SimplexCategory} (σ : n ⟶ m) {x : A.obj n},
      x ∈ obj n → (A.map σ).hom x ∈ obj m) : CosimplicialIdeal A :=
  ⟨obj, map_mem⟩

/-- Evaluation of a cosimplicial ideal constructed from a family recovers that family. -/
theorem ofFamily_obj {A : CosimplicialObject CommRingCat.{u}}
    (obj : (n : SimplexCategory) → Ideal (A.obj n))
    (map_mem : ∀ {n m : SimplexCategory} (σ : n ⟶ m) {x : A.obj n},
      x ∈ obj n → (A.map σ).hom x ∈ obj m) (n : SimplexCategory) :
    (ofFamily obj map_mem).obj n = obj n :=
  rfl

/-- The image of an element of a cosimplicial ideal belongs to the target ideal. -/
theorem mem_map {A : CosimplicialObject CommRingCat.{u}} (I : CosimplicialIdeal A)
    {n m : SimplexCategory} (σ : n ⟶ m) {x : A.obj n} (hx : x ∈ I.obj n) :
    (A.map σ).hom x ∈ I.obj m :=
  I.map_mem σ hx

/-- The ideal at a double-opposite degree of the ring presheaf. -/
def ideal {A : CosimplicialObject CommRingCat.{u}} (I : CosimplicialIdeal A)
    (X : (SimplexCategoryᵒᵖ)ᵒᵖ) : Ideal ((cosimplicialCommRing A).obj X) :=
  I.obj (unop (unop X))

end CosimplicialIdeal

variable {A : CosimplicialObject CommRingCat.{u}}

/-- The ideal-adic completion of a cosimplicial module in one degree. -/
abbrev adicCompletionObj (I : CosimplicialIdeal A)
    (K : PresheafOfModules.{u} (moduleRingPresheaf A)) (n : SimplexCategory) : Type u :=
  AdicCompletion (I.ideal (op (op n))) (K.obj (op (op n)))

namespace CosimplicialModule

variable (I : CosimplicialIdeal A) (K : PresheafOfModules.{u} (moduleRingPresheaf A))

/-- A module structure map sends equivalent representatives modulo an ideal power
to equivalent representatives modulo the target ideal power. -/
private theorem completionQuotientMap_wellDefined
    {X Y : (SimplexCategoryᵒᵖ)ᵒᵖ} (g : X ⟶ Y) (k : ℕ)
    (left right : K.obj X)
    (h : (I.ideal X ^ k • ⊤ : Submodule ((cosimplicialCommRing A).obj X)
      (K.obj X)).quotientRel left right) :
    (Submodule.Quotient.mk (p := (I.ideal Y ^ k • ⊤ :
      Submodule ((cosimplicialCommRing A).obj Y) (K.obj Y))) (K.map g left : K.obj Y)) =
      Submodule.Quotient.mk (p := (I.ideal Y ^ k • ⊤ :
        Submodule ((cosimplicialCommRing A).obj Y) (K.obj Y))) (K.map g right : K.obj Y) := by
  have hI : Ideal.map ((cosimplicialCommRing A).map g).hom (I.ideal X) ≤ I.ideal Y :=
    Ideal.map_le_iff_le_comap.mpr (fun _ hx ↦ I.map_mem g.unop.unop hx)
  have hpow : Ideal.map ((cosimplicialCommRing A).map g).hom (I.ideal X ^ k) ≤
      I.ideal Y ^ k := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono hI k
  apply (Submodule.Quotient.eq _).mpr
  change K.restrictₛₗ g left - K.restrictₛₗ g right ∈
    (I.ideal Y ^ k • ⊤ : Submodule ((cosimplicialCommRing A).obj Y) (K.obj Y))
  rw [← map_sub]
  refine Submodule.smul_induction_on ((Submodule.quotientRel_def _).mp h)
    (fun r hr x _ ↦ ?_) (fun x y hx hy ↦ ?_)
  · rw [map_smulₛₗ]
    exact Submodule.smul_mem_smul (hpow (Ideal.mem_map_of_mem _ hr)) Submodule.mem_top
  · simpa only [map_add] using Submodule.add_mem _ hx hy

/-- The map between ideal-power quotient stages induced by a cosimplicial module map. -/
def completionQuotientMap {X Y : (SimplexCategoryᵒᵖ)ᵒᵖ} (g : X ⟶ Y) (k : ℕ) :
    K.obj X ⧸ (I.ideal X ^ k • ⊤ : Submodule ((cosimplicialCommRing A).obj X) (K.obj X)) →
      K.obj Y ⧸ (I.ideal Y ^ k • ⊤ : Submodule ((cosimplicialCommRing A).obj Y) (K.obj Y)) :=
  fun value ↦ Quotient.liftOn value (fun representative ↦
    Submodule.Quotient.mk (p := (I.ideal Y ^ k • ⊤ :
      Submodule ((cosimplicialCommRing A).obj Y) (K.obj Y))) (K.map g representative : K.obj Y))
    (by exact completionQuotientMap_wellDefined I K g k)

/-- The induced map on ideal-power quotients preserves addition. -/
private theorem completionQuotientMap_map_add
    {X Y : (SimplexCategoryᵒᵖ)ᵒᵖ} (g : X ⟶ Y) (k : ℕ)
    (left right : K.obj X ⧸ (I.ideal X ^ k • ⊤ :
      Submodule ((cosimplicialCommRing A).obj X) (K.obj X))) :
    completionQuotientMap I K g k (left + right) =
      completionQuotientMap I K g k left + completionQuotientMap I K g k right := by
  refine Quotient.inductionOn₂ left right (fun x y ↦ ?_)
  change Submodule.Quotient.mk (p := (I.ideal Y ^ k • ⊤ :
      Submodule ((cosimplicialCommRing A).obj Y) (K.obj Y))) (K.restrictₛₗ g (x + y)) =
    Submodule.Quotient.mk (K.restrictₛₗ g x) + Submodule.Quotient.mk (K.restrictₛₗ g y)
  rw [map_add, Submodule.Quotient.mk_add]

/-- The induced map on ideal-power quotients is semilinear along the ring structure map. -/
private theorem completionQuotientMap_map_smul
    {X Y : (SimplexCategoryᵒᵖ)ᵒᵖ} (g : X ⟶ Y) (k : ℕ)
    (scalar : (cosimplicialCommRing A).obj X)
    (value : K.obj X ⧸ (I.ideal X ^ k • ⊤ :
      Submodule ((cosimplicialCommRing A).obj X) (K.obj X))) :
    completionQuotientMap I K g k (scalar • value) =
      ((cosimplicialCommRing A).map g).hom scalar • completionQuotientMap I K g k value := by
  refine Quotient.inductionOn value (fun x ↦ ?_)
  change Submodule.Quotient.mk (p := (I.ideal Y ^ k • ⊤ :
      Submodule ((cosimplicialCommRing A).obj Y) (K.obj Y))) (K.restrictₛₗ g (scalar • x)) =
    ((cosimplicialCommRing A).map g).hom scalar •
      Submodule.Quotient.mk (K.restrictₛₗ g x)
  have hsmul : K.restrictₛₗ g (scalar • x) =
      ((cosimplicialCommRing A).map g).hom scalar • K.restrictₛₗ g x :=
    K.map_smul g scalar x
  exact congrArg (Submodule.Quotient.mk (p := (I.ideal Y ^ k • ⊤ :
    Submodule ((cosimplicialCommRing A).obj Y) (K.obj Y)))) hsmul

/-- The images of the quotient coordinates of a completed element form a compatible family. -/
private theorem completionMap_compatible {X Y : (SimplexCategoryᵒᵖ)ᵒᵖ} (g : X ⟶ Y)
    (value : AdicCompletion (I.ideal X) (K.obj X)) {lower upper : ℕ}
    (h : lower ≤ upper) :
    AdicCompletion.transitionMap (I.ideal Y) (K.obj Y) h
        (completionQuotientMap I K g upper (value.val upper)) =
      completionQuotientMap I K g lower (value.val lower) := by
  have hcomm (x : K.obj X ⧸ (I.ideal X ^ upper • ⊤ :
      Submodule ((cosimplicialCommRing A).obj X) (K.obj X))) :
      AdicCompletion.transitionMap (I.ideal Y) (K.obj Y) h
          (completionQuotientMap I K g upper x) =
        completionQuotientMap I K g lower
          (AdicCompletion.transitionMap (I.ideal X) (K.obj X) h x) := by
    refine Quotient.inductionOn x (fun x ↦ ?_)
    rfl
  rw [hcomm, value.property h]

/-- A structure map acts on completion by mapping each ideal-power quotient coordinate. -/
def completionMapFun {X Y : (SimplexCategoryᵒᵖ)ᵒᵖ} (g : X ⟶ Y)
    (value : AdicCompletion (I.ideal X) (K.obj X)) :
    AdicCompletion (I.ideal Y) (K.obj Y) :=
  ⟨fun k ↦ completionQuotientMap I K g k (value.val k),
    fun h ↦ by exact completionMap_compatible I K g value h⟩

/-- The coordinatewise structure map on completions preserves addition. -/
private theorem completionMap_add {X Y : (SimplexCategoryᵒᵖ)ᵒᵖ} (g : X ⟶ Y)
    (left right : AdicCompletion (I.ideal X) (K.obj X)) :
    completionMapFun I K g (left + right) =
      completionMapFun I K g left + completionMapFun I K g right := by
  apply AdicCompletion.ext
  intro k
  exact completionQuotientMap_map_add I K g k (left.val k) (right.val k)

/-- The coordinatewise structure map on completions is semilinear along the ring map. -/
private theorem completionMap_smul {X Y : (SimplexCategoryᵒᵖ)ᵒᵖ} (g : X ⟶ Y)
    (scalar : (cosimplicialCommRing A).obj X)
    (value : AdicCompletion (I.ideal X) (K.obj X)) :
    completionMapFun I K g (scalar • value) =
      ((cosimplicialCommRing A).map g).hom scalar • completionMapFun I K g value := by
  apply AdicCompletion.ext
  intro k
  exact completionQuotientMap_map_smul I K g k scalar (value.val k)

/-- The structure map between completed modules, with the target scalars restricted
along the cosimplicial ring structure map. -/
def completionStructureMap {X Y : (SimplexCategoryᵒᵖ)ᵒᵖ} (g : X ⟶ Y) :
    ModuleCat.of ((cosimplicialCommRing A).obj X) (AdicCompletion (I.ideal X) (K.obj X)) ⟶
      (ModuleCat.restrictScalars (R := (cosimplicialCommRing A).obj X)
        (S := (cosimplicialCommRing A).obj Y) ((moduleRingPresheaf A).map g).hom).obj
        (ModuleCat.of ((cosimplicialCommRing A).obj Y) (AdicCompletion (I.ideal Y) (K.obj Y))) :=
  let source := ModuleCat.of ((cosimplicialCommRing A).obj X)
    (AdicCompletion (I.ideal X) (K.obj X))
  let target := (ModuleCat.restrictScalars (R := (cosimplicialCommRing A).obj X)
    (S := (cosimplicialCommRing A).obj Y) ((moduleRingPresheaf A).map g).hom).obj
      (ModuleCat.of ((cosimplicialCommRing A).obj Y) (AdicCompletion (I.ideal Y) (K.obj Y)))
  ModuleCat.ofHom (R := (cosimplicialCommRing A).obj X) (X := source) (Y := target)
    { toFun := completionMapFun I K g
      map_add' := by exact completionMap_add I K g
      map_smul' := by exact completionMap_smul I K g }

/-- The completion structure map for an identity is the canonical identity restriction. -/
private theorem completionStructureMap_id (X : (SimplexCategoryᵒᵖ)ᵒᵖ) :
    completionStructureMap I K (𝟙 X) =
      (ModuleCat.restrictScalarsId' ((moduleRingPresheaf A).map (𝟙 X)).hom
        (congrArg RingCat.Hom.hom ((moduleRingPresheaf A).map_id X))).inv.app _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro value
  apply AdicCompletion.ext
  intro k
  change completionQuotientMap I K (𝟙 X) k (value.val k) = value.val k
  refine Quotient.inductionOn (value.val k) (fun x ↦ ?_)
  exact congrArg (Submodule.Quotient.mk (p := (I.ideal X ^ k • ⊤ :
    Submodule ((cosimplicialCommRing A).obj X) (K.obj X))))
      (show (K.map (𝟙 X) x : K.obj X) = x by rw [K.map_id]; rfl)

/-- Completion structure maps compose through the canonical scalar-restriction comparison. -/
private theorem completionStructureMap_comp {X Y Z : (SimplexCategoryᵒᵖ)ᵒᵖ}
    (first : X ⟶ Y) (second : Y ⟶ Z) :
    completionStructureMap I K (first ≫ second) =
      completionStructureMap I K first ≫
        (ModuleCat.restrictScalars ((moduleRingPresheaf A).map first).hom).map
          (completionStructureMap I K second) ≫
        (ModuleCat.restrictScalarsComp' ((moduleRingPresheaf A).map first).hom
          ((moduleRingPresheaf A).map second).hom ((moduleRingPresheaf A).map (first ≫ second)).hom
          (congrArg RingCat.Hom.hom ((moduleRingPresheaf A).map_comp first second))).inv.app _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro value
  apply AdicCompletion.ext
  intro k
  change completionQuotientMap I K (first ≫ second) k (value.val k) =
    completionQuotientMap I K second k (completionQuotientMap I K first k (value.val k))
  refine Quotient.inductionOn (value.val k) (fun x ↦ ?_)
  exact congrArg (Submodule.Quotient.mk (p := (I.ideal Z ^ k • ⊤ :
    Submodule ((cosimplicialCommRing A).obj Z) (K.obj Z))))
      (K.map_comp_apply first second x)

/-- The degreewise ideal-adic completion of a cosimplicial module as a module presheaf. -/
def adicCompletion : PresheafOfModules.{u} (moduleRingPresheaf A) where
  obj X := ModuleCat.of ((cosimplicialCommRing A).obj X) (AdicCompletion (I.ideal X) (K.obj X))
  map g := completionStructureMap I K g
  map_id X := by exact completionStructureMap_id I K X
  map_comp first second := by exact completionStructureMap_comp I K first second

variable {K M : PresheafOfModules.{u} (moduleRingPresheaf A)}

/-- Degreewise completion of a module morphism commutes with the completion structure maps. -/
private theorem adicCompletionMap_naturality (φ : K ⟶ M)
    {X Y : (SimplexCategoryᵒᵖ)ᵒᵖ} (g : X ⟶ Y) :
    (adicCompletion I K).map g ≫
        (ModuleCat.restrictScalars ((moduleRingPresheaf A).map g).hom).map
          (ModuleCat.ofHom ((AdicCompletion.map (I.ideal Y) (φ.app Y).hom).restrictScalars
            ((cosimplicialCommRing A).obj Y))) =
      ModuleCat.ofHom ((AdicCompletion.map (I.ideal X) (φ.app X).hom).restrictScalars
        ((cosimplicialCommRing A).obj X)) ≫ (adicCompletion I M).map g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro value
  apply AdicCompletion.ext
  intro k
  change (φ.app Y).hom.reduceModIdeal (I.ideal Y ^ k)
      (completionQuotientMap I K g k (value.val k)) =
    completionQuotientMap I M g k
      ((φ.app X).hom.reduceModIdeal (I.ideal X ^ k) (value.val k))
  refine Quotient.inductionOn (value.val k) (fun x ↦ ?_)
  exact congrArg (Submodule.Quotient.mk (p := (I.ideal Y ^ k • ⊤ :
    Submodule ((cosimplicialCommRing A).obj Y) (M.obj Y))))
      (PresheafOfModules.naturality_apply φ g x)

/-- A module morphism induces a module morphism on degreewise ideal-adic completions. -/
def adicCompletionMap (φ : K ⟶ M) : adicCompletion I K ⟶ adicCompletion I M where
  app X := ModuleCat.ofHom ((AdicCompletion.map (I.ideal X) (φ.app X).hom).restrictScalars
    ((cosimplicialCommRing A).obj X))
  naturality g := by exact adicCompletionMap_naturality I φ g

end CosimplicialModule

/-- The additive cosimplicial object underlying degreewise ideal-adic completion. -/
abbrev adicCompletion (I : CosimplicialIdeal A)
    (K : PresheafOfModules.{u} (moduleRingPresheaf A)) : CosimplicialObject Ab :=
  underlyingAb (CosimplicialModule.adicCompletion I K)

/-- The additive completion in each degree is the ordinary completion of its section module. -/
theorem adicCompletion_obj (I : CosimplicialIdeal A)
    (K : PresheafOfModules.{u} (moduleRingPresheaf A)) (n : SimplexCategory) :
    (adicCompletion I K).obj n = AddCommGrpCat.of (adicCompletionObj I K n) :=
  rfl

variable {K M : PresheafOfModules.{u} (moduleRingPresheaf A)}

/-- The additive morphism underlying completion of a cosimplicial module morphism. -/
abbrev adicCompletionMap (I : CosimplicialIdeal A) (φ : K ⟶ M) :
    adicCompletion I K ⟶ adicCompletion I M :=
  underlyingHom (CosimplicialModule.adicCompletionMap I φ)

/-- The additive components of completion maps are ordinary completion maps. -/
theorem adicCompletionMap_app (I : CosimplicialIdeal A) (φ : K ⟶ M)
    (n : SimplexCategory) :
    (adicCompletionMap I φ).app n = AddCommGrpCat.ofHom
      ((AdicCompletion.map (I.ideal (op (op n))) (φ.app (op (op n))).hom).toAddMonoidHom) :=
  rfl

/-- Completion sends the identity module morphism to the identity additive morphism. -/
theorem adicCompletionMap_id (I : CosimplicialIdeal A)
    (K : PresheafOfModules.{u} (moduleRingPresheaf A)) :
    adicCompletionMap I (𝟙 K) = 𝟙 (adicCompletion I K) := by
  ext n : 1
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro value
  change AdicCompletion.map (I.ideal (op (op n)))
    (LinearMap.id (M := K.obj (op (op n)))) value = value
  rw [AdicCompletion.map_id]
  rfl
