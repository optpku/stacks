/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Amitsur.CosimplicialModule
public import ReasLib.Algebra.Category.ModuleCat.Descent.BaseExtension
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Cosimplicial

/-!
# Cartesian Amitsur modules from descent data

This file constructs the functor from module descent data to cartesian modules over the
Amitsur cosimplicial algebra and packages it as an equivalence of categories.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite
open scoped ChangeOfRings TensorProduct

universe u

namespace Algebra.Amitsur.Descent

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- The unique module component of canonical descent data along `R → A`. -/
abbrev component (D : ModuleCat.DescentData (Algebra.ofId R A).toRingHom) :
    ModuleCat.{u} A :=
  D.obj PUnit.unit

/-- The component abbreviation recovers the unique object of the singleton descent family. -/
theorem component_def (D : ModuleCat.DescentData (Algebra.ofId R A).toRingHom) :
    component D = D.obj PUnit.unit := sorry

/-- The degree-`Δ` scalar extension of the unique module component of canonical descent data
along the vertex `i`. -/
noncomputable abbrev termAt
    (D : ModuleCat.DescentData (Algebra.ofId R A).toRingHom)
    (Δ : SimplexCategory) (i : Fin (Δ.len + 1)) :
    ModuleCat.{u} ((Algebra.Amitsur.cosimplicialCommRing R A).obj Δ) :=
  (ModuleCat.extendScalars (Algebra.Amitsur.vertex R A Δ i)).obj (component D)

/-- `termAt` is the scalar extension of the unique component of the descent datum. -/
theorem termAt_def (D : ModuleCat.DescentData (Algebra.ofId R A).toRingHom)
    (Δ : SimplexCategory) (i : Fin (Δ.len + 1)) :
    termAt D Δ i =
      (ModuleCat.extendScalars (Algebra.Amitsur.vertex R A Δ i)).obj
        (component D) := sorry

/-- Canonical descent data identify the scalar extensions along any two vertices of one
Amitsur degree. -/
noncomputable def transitionToLast
    (D : ModuleCat.DescentData (Algebra.ofId R A).toRingHom)
    (Γ : SimplexCategory) (i : Fin (Γ.len + 1)) :
    termAt D Γ i ≅ termAt D Γ (Fin.last Γ.len) :=
  D.iso
    ((CommRingCat.ofHom
      (algebraMap R ((Algebra.Amitsur.cosimplicialAlgebra R A).obj Γ))).op)
    ((CommRingCat.ofHom (Algebra.Amitsur.vertex R A Γ i)).op)
    ((CommRingCat.ofHom
      (Algebra.Amitsur.vertex R A Γ (Fin.last Γ.len))).op)
    (Algebra.Amitsur.vertex_overBase Γ i)
    (Algebra.Amitsur.vertex_overBase Γ (Fin.last Γ.len))

/-- The forward map of `transitionToLast` is the transition supplied by the descent datum. -/
theorem transitionToLast_hom
    (D : ModuleCat.DescentData (Algebra.ofId R A).toRingHom)
    (Γ : SimplexCategory) (i : Fin (Γ.len + 1)) :
    (transitionToLast D Γ i).hom =
      D.hom
        ((CommRingCat.ofHom
          (algebraMap R ((Algebra.Amitsur.cosimplicialAlgebra R A).obj Γ))).op)
        ((CommRingCat.ofHom (Algebra.Amitsur.vertex R A Γ i)).op)
        ((CommRingCat.ofHom
          (Algebra.Amitsur.vertex R A Γ (Fin.last Γ.len))).op)
        (Algebra.Amitsur.vertex_overBase Γ i)
        (Algebra.Amitsur.vertex_overBase Γ (Fin.last Γ.len)) := sorry

/-- Reindex the last-vertex module along a simplex morphism. -/
noncomputable def reindexLast
    (D : ModuleCat.DescentData (Algebra.ofId R A).toRingHom)
    {Δ Γ : SimplexCategory} (β : Δ ⟶ Γ) :
    termAt D Δ (Fin.last Δ.len) ⟶
      (ModuleCat.restrictScalars
        ((Algebra.Amitsur.cosimplicialCommRing R A).map β).hom).obj
          (termAt D Γ (β.toOrderHom (Fin.last Δ.len))) :=
  let target :=
    (ModuleCat.restrictScalars
      ((Algebra.Amitsur.cosimplicialCommRing R A).map β).hom).obj
        (termAt D Γ (β.toOrderHom (Fin.last Δ.len)))
  let generator : component D ⟶
      (ModuleCat.restrictScalars
        (Algebra.Amitsur.vertex R A Δ (Fin.last Δ.len))).obj target :=
    (ModuleCat.extendRestrictScalarsAdj
      (Algebra.Amitsur.vertex R A Γ
        (β.toOrderHom (Fin.last Δ.len)))).unit.app (component D) ≫
      (ModuleCat.restrictScalarsComp'App
        (Algebra.Amitsur.vertex R A Δ (Fin.last Δ.len))
        ((Algebra.Amitsur.cosimplicialCommRing R A).map β).hom
        (Algebra.Amitsur.vertex R A Γ
          (β.toOrderHom (Fin.last Δ.len)))
        (Algebra.Amitsur.vertex_map β (Fin.last Δ.len))
        (termAt D Γ (β.toOrderHom (Fin.last Δ.len)))).hom
  ((ModuleCat.extendRestrictScalarsAdj
    (Algebra.Amitsur.vertex R A Δ (Fin.last Δ.len))).homEquiv _ _).symm generator

/-- The Amitsur structure map first reindexes and then applies the descent transition. -/
noncomputable def structureMap
    (D : ModuleCat.DescentData (Algebra.ofId R A).toRingHom)
    {Δ Γ : SimplexCategory} (β : Δ ⟶ Γ) :
    termAt D Δ (Fin.last Δ.len) ⟶
      (ModuleCat.restrictScalars
        ((Algebra.Amitsur.cosimplicialCommRing R A).map β).hom).obj
          (termAt D Γ (Fin.last Γ.len)) :=
  reindexLast D β ≫
    (ModuleCat.restrictScalars
      ((Algebra.Amitsur.cosimplicialCommRing R A).map β).hom).map
        (transitionToLast D Γ (β.toOrderHom (Fin.last Δ.len))).hom

/-- Canonical module descent data determine a module over the Amitsur cosimplicial algebra. -/
noncomputable def cosimplicial
    (D : ModuleCat.DescentData (Algebra.ofId R A).toRingHom) :
    CosimplicialAlgebra.Module (Algebra.Amitsur.cosimplicialAlgebra R A) where
  obj X := termAt D (unop (unop X)) (Fin.last (unop (unop X)).len)
  map f := structureMap D f.unop.unop
  map_id := sorry
  map_comp := sorry

/-- Evaluation of the associated cosimplicial module is its last-vertex scalar extension. -/
theorem cosimplicial_obj
    (D : ModuleCat.DescentData (Algebra.ofId R A).toRingHom)
    (Δ : SimplexCategory) :
    CosimplicialAlgebra.Module.eval (cosimplicial D) Δ =
      termAt D Δ (Fin.last Δ.len) := sorry

/-- A morphism of canonical descent data induces a morphism of Amitsur cosimplicial modules. -/
noncomputable def cosimplicialMap
    {D E : ModuleCat.DescentData (Algebra.ofId R A).toRingHom} (f : D ⟶ E) :
    cosimplicial D ⟶ cosimplicial E where
  app X := (ModuleCat.extendScalars
    (Algebra.Amitsur.vertex R A (unop (unop X))
      (Fin.last (unop (unop X)).len))).map (f.hom PUnit.unit)
  naturality := sorry

/-- The component of `cosimplicialMap` is scalar extension of the unique descent-data
component. -/
theorem cosimplicialMap_app
    {D E : ModuleCat.DescentData (Algebra.ofId R A).toRingHom} (f : D ⟶ E)
    (Δ : SimplexCategory) :
    PresheafOfModules.Hom.app (cosimplicialMap f) (op (op Δ)) =
      (ModuleCat.extendScalars
        (Algebra.Amitsur.vertex R A Δ (Fin.last Δ.len))).map
          (f.hom PUnit.unit) := sorry

/-- The functor from canonical module descent data to modules over the Amitsur cosimplicial
algebra. -/
noncomputable def toModule : ModuleCat.DescentData (Algebra.ofId R A).toRingHom ⥤
    CosimplicialAlgebra.Module (Algebra.Amitsur.cosimplicialAlgebra R A) where
  obj := cosimplicial
  map := cosimplicialMap
  map_id := sorry
  map_comp := sorry

/-- Scalar extension of a last-vertex term along a simplex map is the term at the image
vertex. -/
noncomputable def reindexLastIso
    (D : ModuleCat.DescentData (Algebra.ofId R A).toRingHom)
    {Δ Γ : SimplexCategory} (β : Δ ⟶ Γ) :
    (ModuleCat.extendScalars
      ((Algebra.Amitsur.cosimplicialCommRing R A).map β).hom).obj
        (termAt D Δ (Fin.last Δ.len)) ≅
      termAt D Γ (β.toOrderHom (Fin.last Δ.len)) :=
  (ModuleCat.extendScalarsComp
      (Algebra.Amitsur.vertex R A Δ (Fin.last Δ.len))
      ((Algebra.Amitsur.cosimplicialCommRing R A).map β).hom).symm.app (component D) ≪≫
    eqToIso (congrArg (fun g : A →+* _ ↦ (ModuleCat.extendScalars g).obj (component D))
      (Algebra.Amitsur.vertex_map β (Fin.last Δ.len)).symm)

/-- The base-change comparison for a descent datum has inverse given by the reversed
descent transition followed by inverse scalar-extension composition. -/
noncomputable def baseChangeIso
    (D : ModuleCat.DescentData (Algebra.ofId R A).toRingHom)
    {Δ Γ : SimplexCategory} (β : Δ ⟶ Γ) :
    (ModuleCat.extendScalars
      ((Algebra.Amitsur.cosimplicialCommRing R A).map β).hom).obj
        (termAt D Δ (Fin.last Δ.len)) ≅ termAt D Γ (Fin.last Γ.len) where
  hom := CosimplicialAlgebra.Module.baseChangeMap (cosimplicial D) β
  inv := (transitionToLast D Γ (β.toOrderHom (Fin.last Δ.len))).inv ≫
    (reindexLastIso D β).inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward comparison is the adjoint transpose of the cosimplicial structure map. -/
theorem baseChangeIso_hom
    (D : ModuleCat.DescentData (Algebra.ofId R A).toRingHom)
    {Δ Γ : SimplexCategory} (β : Δ ⟶ Γ) :
    (baseChangeIso D β).hom =
      CosimplicialAlgebra.Module.baseChangeMap (cosimplicial D) β := rfl

/-- Every Amitsur cosimplicial module obtained from canonical descent data is cartesian. -/
theorem toModule_isCartesian
    (D : ModuleCat.DescentData (Algebra.ofId R A).toRingHom) :
    CosimplicialAlgebra.Module.IsCartesian ((toModule).obj D) := by
  intro Δ Γ β
  exact (baseChangeIso D β.unop.unop).isIso_hom

/-- The functor from canonical module descent data to cartesian modules over the Amitsur
cosimplicial algebra. -/
noncomputable def toCartesian : ModuleCat.DescentData (Algebra.ofId R A).toRingHom ⥤
    CosimplicialAlgebra.CartesianModule (Algebra.Amitsur.cosimplicialAlgebra R A) :=
  ObjectProperty.lift
    (fun M : CosimplicialAlgebra.Module (Algebra.Amitsur.cosimplicialAlgebra R A) ↦
      CosimplicialAlgebra.Module.IsCartesian M) toModule toModule_isCartesian

/-- A ring map out of an Amitsur degree, determined by compatible values on the vertices. -/
noncomputable def vertexDesc (Δ : SimplexCategory) {B : Type u} [CommRing B] (r : R →+* B)
    (a : Fin (Δ.len + 1) → (A →+* B)) (ha : ∀ j, (a j).comp (algebraMap R A) = r) :
    (Algebra.Amitsur.cosimplicialCommRing R A).obj Δ →+* B :=
  -- Local instance justification (noncanonical choice): the supplied map `r` determines the
  -- target algebra for the wide-pushout universal property.
  letI : Algebra R B := r.toAlgebra
  (Limits.WidePushout.desc
    (arrows := fun _ : Fin (Δ.len + 1) ↦ CommAlgCat.ofHom (Algebra.ofId R A))
    (CommAlgCat.ofHom (Algebra.ofId R B))
    (fun j ↦ CommAlgCat.ofHom
      { toRingHom := a j
        commutes' := fun x ↦ congrArg (fun g : R →+* B ↦ g x) (ha j) })
    (fun _ ↦ CommAlgCat.hom_ext (Subsingleton.elim _ _))).hom.toRingHom

/-- `vertexDesc` takes the prescribed value on every vertex. -/
theorem vertexDesc_comp_vertex (Δ : SimplexCategory) {B : Type u} [CommRing B] (r : R →+* B)
    (a : Fin (Δ.len + 1) → (A →+* B)) (ha : ∀ j, (a j).comp (algebraMap R A) = r)
    (j : Fin (Δ.len + 1)) :
    (vertexDesc Δ r a ha).comp (Algebra.Amitsur.vertex R A Δ j) = a j := sorry

/-- The inverse `A₀ → A` of the unique vertex of the degree-zero Amitsur ring. -/
noncomputable def degreeZeroToBase :
    (Algebra.Amitsur.cosimplicialCommRing R A).obj (SimplexCategory.mk 0) →+* A :=
  vertexDesc (SimplexCategory.mk 0) (algebraMap R A) (fun _ ↦ RingHom.id A)
    (fun _ ↦ RingHom.id_comp _)

/-- `degreeZeroToBase` is left inverse to the unique degree-zero vertex. -/
theorem degreeZeroToBase_comp_vertex :
    (degreeZeroToBase (R := R) (A := A)).comp
        (Algebra.Amitsur.vertex R A (SimplexCategory.mk 0) (Fin.last 0)) =
      RingHom.id A := sorry

/-- The ring map of the coface `[0] → [n]` selecting the vertex `j`. -/
noncomputable abbrev coface (Δ : SimplexCategory) (j : Fin (Δ.len + 1)) :
    (Algebra.Amitsur.cosimplicialCommRing R A).obj (SimplexCategory.mk 0) →+*
      (Algebra.Amitsur.cosimplicialCommRing R A).obj Δ :=
  ((Algebra.Amitsur.cosimplicialCommRing R A).map
    (SimplexCategory.const (SimplexCategory.mk 0) Δ j)).hom

/-- After `degreeZeroToBase`, a vertex of degree `Δ` is the corresponding coface map. -/
theorem vertex_comp_degreeZeroToBase (Δ : SimplexCategory) (j : Fin (Δ.len + 1)) :
    (Algebra.Amitsur.vertex R A Δ j).comp degreeZeroToBase = coface Δ j := sorry

/-- A map out of the degree-one Amitsur ring restricts along a coface to the corresponding
vertex value, transported through `degreeZeroToBase`. -/
theorem comp_degreeZeroToBase_eq {B : Type u} [CommRing B]
    (c : (Algebra.Amitsur.cosimplicialCommRing R A).obj (SimplexCategory.mk 1) →+* B)
    (a : A →+* B) (j : Fin 2)
    (hc : c.comp (Algebra.Amitsur.vertex R A (SimplexCategory.mk 1) j) = a) :
    a.comp degreeZeroToBase = c.comp (coface (SimplexCategory.mk 1) j) := sorry

/-- A ring map from `A` that lies over the descent family `R → A` is an `R`-algebra map for
the structure induced by the base map. -/
theorem overBase {Y : CommRingCat.{u}ᵒᵖ} {q : Y ⟶ Opposite.op (CommRingCat.of R)}
    (g : Y ⟶ Opposite.op (CommRingCat.of A))
    (hg : g ≫ ModuleCat.descentFamily (Algebra.ofId R A).toRingHom PUnit.unit = q) :
    g.unop.hom.comp (algebraMap R A) = q.unop.hom := sorry

/-- The degree-zero term of a cartesian Amitsur module. -/
abbrev degreeZero
    (M : CosimplicialAlgebra.CartesianModule (Algebra.Amitsur.cosimplicialAlgebra R A)) :
    ModuleCat.{u} ((Algebra.Amitsur.cosimplicialCommRing R A).obj (SimplexCategory.mk 0)) :=
  CosimplicialAlgebra.Module.eval M.obj (SimplexCategory.mk 0)

/-- The `A`-module underlying the descent datum of a cartesian Amitsur module: its degree-zero
term transported along `A₀ ≅ A`. -/
noncomputable abbrev descentComponent
    (M : CosimplicialAlgebra.CartesianModule (Algebra.Amitsur.cosimplicialAlgebra R A)) :
    ModuleCat.{u} A :=
  (ModuleCat.extendScalars degreeZeroToBase).obj (degreeZero M)

/-- The ring map out of the degree-one Amitsur ring with vertex values `a₁` and `a₂`. -/
noncomputable abbrev pairDesc {B : Type u} [CommRing B] (r : R →+* B) (a₁ a₂ : A →+* B)
    (h₁ : a₁.comp (algebraMap R A) = r) (h₂ : a₂.comp (algebraMap R A) = r) :
    (Algebra.Amitsur.cosimplicialCommRing R A).obj (SimplexCategory.mk 1) →+* B :=
  vertexDesc (SimplexCategory.mk 1) r ![a₁, a₂]
    (Fin.cases (motive := fun j ↦ (![a₁, a₂] j).comp (algebraMap R A) = r) h₁
      (fun k ↦ by obtain rfl : k = 0 := Subsingleton.elim _ _; exact h₂))

/-- The descent transition of a cartesian Amitsur module over two maps `a₁ a₂ : A → B`
agreeing on `R`: identify both scalar extensions with the scalar extension of the degree-one
term along the pair map `A₁ → B`, using the cartesian comparisons of the two cofaces. -/
noncomputable def descentHom
    (M : CosimplicialAlgebra.CartesianModule (Algebra.Amitsur.cosimplicialAlgebra R A))
    {B : Type u} [CommRing B] (r : R →+* B) (a₁ a₂ : A →+* B)
    (h₁ : a₁.comp (algebraMap R A) = r) (h₂ : a₂.comp (algebraMap R A) = r) :
    (ModuleCat.extendScalars a₁).obj (descentComponent M) ⟶
      (ModuleCat.extendScalars a₂).obj (descentComponent M) :=
  let c := pairDesc r a₁ a₂ h₁ h₂
  let M₀ := degreeZero M
  (ModuleCat.extendScalarsComp degreeZeroToBase a₁).inv.app M₀ ≫
    eqToHom (congrArg (fun g ↦ (ModuleCat.extendScalars g).obj M₀)
      (comp_degreeZeroToBase_eq c a₁ 0 (vertexDesc_comp_vertex _ _ _ _ 0))) ≫
    (ModuleCat.extendScalarsComp (coface (SimplexCategory.mk 1) 0) c).hom.app M₀ ≫
    (ModuleCat.extendScalars c).map
      (CosimplicialAlgebra.Module.baseChangeMap M.obj
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 0)) ≫
    (ModuleCat.extendScalars c).map
      (CosimplicialAlgebra.CartesianModule.baseChangeIso M
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 1)).inv ≫
    (ModuleCat.extendScalarsComp (coface (SimplexCategory.mk 1) 1) c).inv.app M₀ ≫
    eqToHom (congrArg (fun g ↦ (ModuleCat.extendScalars g).obj M₀)
      (comp_degreeZeroToBase_eq c a₂ 1 (vertexDesc_comp_vertex _ _ _ _ 1)).symm) ≫
    (ModuleCat.extendScalarsComp degreeZeroToBase a₂).hom.app M₀

/-- The canonical descent datum of a cartesian Amitsur module. -/
noncomputable def ofCartesianObj
    (M : CosimplicialAlgebra.CartesianModule (Algebra.Amitsur.cosimplicialAlgebra R A)) :
    ModuleCat.DescentData (Algebra.ofId R A).toRingHom where
  obj _ := descentComponent (R := R) (A := A) M
  hom _ q _ _ f₁ f₂ hf₁ hf₂ :=
    descentHom M q.unop.hom (f₁.unop.hom : A →+* _) (f₂.unop.hom : A →+* _)
      (overBase f₁ hf₁) (overBase f₂ hf₂)
  pullHom_hom := sorry
  hom_self := sorry
  hom_comp := sorry

/-- The unique component of `ofCartesianObj` is the transported degree-zero term. -/
theorem ofCartesianObj_obj
    (M : CosimplicialAlgebra.CartesianModule (Algebra.Amitsur.cosimplicialAlgebra R A)) :
    (ofCartesianObj M).obj PUnit.unit = descentComponent M := rfl

/-- A morphism of cartesian Amitsur modules induces a morphism of descent data through its
degree-zero component. -/
noncomputable def ofCartesianMap
    {M M' : CosimplicialAlgebra.CartesianModule
      (Algebra.Amitsur.cosimplicialAlgebra R A)} (φ : M ⟶ M') :
    ofCartesianObj M ⟶ ofCartesianObj M' where
  hom _ := (ModuleCat.extendScalars degreeZeroToBase).map
    (PresheafOfModules.Hom.app φ.hom (op (op (SimplexCategory.mk 0))))
  comm := sorry

/-- The inverse functor recovering canonical module descent data from a cartesian Amitsur
module. -/
noncomputable def ofCartesian :
    CosimplicialAlgebra.CartesianModule (Algebra.Amitsur.cosimplicialAlgebra R A) ⥤
      ModuleCat.DescentData (Algebra.ofId R A).toRingHom where
  obj := ofCartesianObj
  map := ofCartesianMap
  map_id := sorry
  map_comp := sorry

/-- The unique module of the inverse functor is the scalar extension of the degree-zero
term along the inverse degree-zero vertex. -/
theorem ofCartesian_obj_obj
    (M : CosimplicialAlgebra.CartesianModule (Algebra.Amitsur.cosimplicialAlgebra R A)) :
    (ofCartesian.obj M).obj PUnit.unit =
      (ModuleCat.extendScalars degreeZeroToBase).obj (degreeZero M) := rfl

/-- The inverse functor acts on morphisms by scalar extension of their degree-zero
components. -/
theorem ofCartesian_map_hom
    {M M' : CosimplicialAlgebra.CartesianModule (Algebra.Amitsur.cosimplicialAlgebra R A)}
    (φ : M ⟶ M') :
    (ofCartesian.map φ).hom PUnit.unit =
      (ModuleCat.extendScalars degreeZeroToBase).map
        (PresheafOfModules.Hom.app φ.hom (op (op (SimplexCategory.mk 0)))) := rfl

/-- The unit component: a descent datum is recovered from the degree-zero term of its
cartesian Amitsur module, using `A₀ ≅ A`. -/
noncomputable def unitIsoApp (D : ModuleCat.DescentData (Algebra.ofId R A).toRingHom) :
    D ≅ ofCartesian.obj (toCartesian.obj D) :=
  Pseudofunctor.DescentData.isoMk
    (fun _ ↦ ((ModuleCat.extendScalarsId A).app (component D)).symm ≪≫
      eqToIso (congrArg (fun g ↦ (ModuleCat.extendScalars g).obj (component D))
        (degreeZeroToBase_comp_vertex (R := R) (A := A)).symm) ≪≫
      (ModuleCat.extendScalarsComp
        (Algebra.Amitsur.vertex R A (SimplexCategory.mk 0) (Fin.last 0))
        degreeZeroToBase).app (component D))
    sorry

/-- The counit component in degree `Δ`: the last-vertex extension of the transported
degree-zero term is identified with `M_Δ` by the cartesian comparison along the coface
`[0] → Δ`. -/
noncomputable def counitComponent
    (M : CosimplicialAlgebra.CartesianModule (Algebra.Amitsur.cosimplicialAlgebra R A))
    (Δ : SimplexCategory) :
    termAt (ofCartesianObj M) Δ (Fin.last Δ.len) ≅
      CosimplicialAlgebra.Module.eval M.obj Δ :=
  (ModuleCat.extendScalarsComp degreeZeroToBase
      (Algebra.Amitsur.vertex R A Δ (Fin.last Δ.len))).symm.app (degreeZero M) ≪≫
    eqToIso (congrArg
      (fun g : (Algebra.Amitsur.cosimplicialCommRing R A).obj (SimplexCategory.mk 0) →+*
          (Algebra.Amitsur.cosimplicialCommRing R A).obj Δ ↦
        (ModuleCat.extendScalars g).obj (degreeZero M))
      (vertex_comp_degreeZeroToBase Δ (Fin.last Δ.len))) ≪≫
    CosimplicialAlgebra.CartesianModule.baseChangeIso M
      (SimplexCategory.const (SimplexCategory.mk 0) Δ (Fin.last Δ.len))

/-- The counit: the cartesian module of `ofCartesian M` is identified with `M` degreewise by
`counitComponent`. -/
noncomputable def counitIsoApp
    (M : CosimplicialAlgebra.CartesianModule (Algebra.Amitsur.cosimplicialAlgebra R A)) :
    toCartesian.obj (ofCartesian.obj M) ≅ M :=
  ObjectProperty.isoMk _ <| PresheafOfModules.isoMk
    (fun X ↦ counitComponent M (unop (unop X)))
    sorry

/-- Canonical module descent data are equivalent to cartesian modules over the Amitsur
cosimplicial algebra. -/
noncomputable def equivalence :
    ModuleCat.DescentData (Algebra.ofId R A).toRingHom ≌
      CosimplicialAlgebra.CartesianModule (Algebra.Amitsur.cosimplicialAlgebra R A) where
  functor := toCartesian
  inverse := ofCartesian
  unitIso := NatIso.ofComponents unitIsoApp sorry
  counitIso := NatIso.ofComponents counitIsoApp sorry
  functor_unitIso_comp := sorry

/-- The canonical functor from module descent data to cartesian Amitsur modules is an
equivalence. -/
instance toCartesian_isEquivalence :
    (toCartesian : ModuleCat.DescentData (Algebra.ofId R A).toRingHom ⥤
      CosimplicialAlgebra.CartesianModule
        (Algebra.Amitsur.cosimplicialAlgebra R A)).IsEquivalence :=
  (equivalence (R := R) (A := A)).isEquivalence_functor

/-- The forward functor of `equivalence` is `toCartesian`. -/
theorem equivalence_functor :
    (equivalence (R := R) (A := A)).functor = toCartesian := rfl

/-- The inverse functor of `equivalence` is `ofCartesian`. -/
theorem equivalence_inverse :
    (equivalence (R := R) (A := A)).inverse = ofCartesian := rfl

end Algebra.Amitsur.Descent
