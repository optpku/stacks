/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.HomComplex.Derived.Over
import Mathlib.Tactic.CrossRefAttribute

/-!
# Carrier-polymorphic canonical `RHom`

The short module facade in `Model.RHom` is intentionally aligned with the standard same-universe
derived category.  This leaf keeps the carrier universe explicit, so scalar extension and other
cross-universe constructions can use one canonical two-variable owner without changing the legacy
API.

@stack 0E1U
-/

@[expose] public section

noncomputable section

universe r v

open CategoryTheory

namespace CategoryTheory.DerivedCategory.InternalHom.RHom.At

variable {R : Type r} [CommRing R]

/-- `0E1U:` The derived category of `R`-modules with an explicit carrier universe. -/
@[stacks 0E1U "carrier-polymorphic derived module category"]
abbrev Derived :=
  DerivedCategory.{max (v + 1) r, v, max (v + 1) r} (ModuleCat.{v, r} R)

/-- `0E1U:` Existence of carrier-polymorphic canonical derived enriched Hom. -/
@[stacks 0E1U "carrier-polymorphic canonical RHom availability"]
abbrev Has : Prop :=
  CochainComplex.Enriched.Over.RHom.Has (R := R) (C := ModuleCat.{v, r} R)

/-- `0E1U:` The carrier-polymorphic canonical derived `RHom` bifunctor. -/
@[stacks 0E1U "carrier-polymorphic canonical RHom bifunctor"]
noncomputable abbrev functor [Has.{r, v} (R := R)] :
    (Derived.{r, v} (R := R))ᵒᵖ × Derived.{r, v} (R := R) ⥤ Derived.{r, v} (R := R) :=
  CochainComplex.Enriched.Over.RHom.functor
    (R := R) (C := ModuleCat.{v, r} R)

/-- The carrier-polymorphic canonical `RHom`, curried in its target variable. -/
@[stacks 0E1U "carrier-polymorphic curried canonical RHom"]
noncomputable abbrev curried [Has.{r, v} (R := R)] :
    (Derived.{r, v} (R := R))ᵒᵖ ⥤ Derived.{r, v} (R := R) ⥤ Derived.{r, v} (R := R) :=
  CochainComplex.Enriched.Over.RHom.curried
    (R := R) (C := ModuleCat.{v, r} R)

/-- The carrier-polymorphic canonical `RHom(-, L)` source-variable functor. -/
@[stacks 0E1U "carrier-polymorphic source-variable canonical RHom"]
noncomputable abbrev sourceFunctor (L : Derived.{r, v} (R := R))
    [Has.{r, v} (R := R)] :
    (Derived.{r, v} (R := R))ᵒᵖ ⥤ Derived.{r, v} (R := R) :=
  CochainComplex.Enriched.Over.RHom.sourceFunctor
    (R := R) (C := ModuleCat.{v, r} R) L

/-- The carrier-polymorphic canonical `RHom(K, -)` target-variable functor. -/
@[stacks 0E1U "carrier-polymorphic target-variable canonical RHom"]
noncomputable abbrev targetFunctor (K : Derived.{r, v} (R := R))
    [Has.{r, v} (R := R)] :
    Derived.{r, v} (R := R) ⥤ Derived.{r, v} (R := R) :=
  CochainComplex.Enriched.Over.RHom.targetFunctor
    (R := R) (C := ModuleCat.{v, r} R) (Opposite.op K)

/-- The carrier-polymorphic canonical object `RHom_R(K,L)`. -/
@[stacks 0E1U "carrier-polymorphic canonical RHom object"]
noncomputable abbrev obj
    (K L : Derived.{r, v} (R := R)) [Has.{r, v} (R := R)] :
      Derived.{r, v} (R := R) :=
  (targetFunctor (R := R) K).obj L

/-- The carrier-polymorphic canonical map, contravariant in the source and covariant in the target. -/
@[stacks 0E1U "carrier-polymorphic canonical RHom map"]
noncomputable abbrev map
    {K₁ K₂ L₁ L₂ : Derived.{r, v} (R := R)}
    (fK : K₂ ⟶ K₁) (fL : L₁ ⟶ L₂) [Has.{r, v} (R := R)] :
    obj (R := R) K₁ L₁ ⟶ obj (R := R) K₂ L₂ :=
  (functor (R := R)).map (fK.op, fL)

/-- Precomposition on carrier-polymorphic canonical `RHom`. -/
@[stacks 0E1U "carrier-polymorphic canonical RHom precomposition"]
noncomputable abbrev pre
    {K₁ K₂ : Derived.{r, v} (R := R)} (fK : K₂ ⟶ K₁)
    [Has.{r, v} (R := R)] :
    targetFunctor (R := R) K₁ ⟶ targetFunctor (R := R) K₂ :=
  (curried (R := R)).map fK.op

/-- Postcomposition on carrier-polymorphic canonical `RHom`. -/
@[stacks 0E1U "carrier-polymorphic canonical RHom postcomposition"]
noncomputable abbrev post
    {L₁ L₂ : Derived.{r, v} (R := R)} (fL : L₁ ⟶ L₂)
    [Has.{r, v} (R := R)] :
    sourceFunctor (R := R) L₁ ⟶ sourceFunctor (R := R) L₂ :=
  (curried (R := R)).flip.map fL

/-- The source-variable object formula for carrier-polymorphic canonical `RHom`. -/
@[simp, stacks 0E1U "carrier-polymorphic RHom source object formula"]
theorem sourceFunctor_obj
    (K L : Derived.{r, v} (R := R)) [Has.{r, v} (R := R)] :
    (sourceFunctor (R := R) L).obj (Opposite.op K) = obj (R := R) K L := rfl

/-- The target-variable object formula for carrier-polymorphic canonical `RHom`. -/
@[simp, stacks 0E1U "carrier-polymorphic RHom target object formula"]
theorem targetFunctor_obj
    (K L : Derived.{r, v} (R := R)) [Has.{r, v} (R := R)] :
    (targetFunctor (R := R) K).obj L = obj (R := R) K L := rfl

/-- Source-variable maps are the first components of the carrier-polymorphic canonical map. -/
@[simp, stacks 0E1U "carrier-polymorphic RHom source map formula"]
theorem sourceFunctor_map
    {K₁ K₂ : Derived.{r, v} (R := R)} (fK : K₂ ⟶ K₁)
    (L : Derived.{r, v} (R := R)) [Has.{r, v} (R := R)] :
    (sourceFunctor (R := R) L).map fK.op = map (R := R) fK (𝟙 L) := rfl

/-- Target-variable maps are the second components of the carrier-polymorphic canonical map. -/
@[simp, stacks 0E1U "carrier-polymorphic RHom target map formula"]
theorem targetFunctor_map
    (K : Derived.{r, v} (R := R))
    {L₁ L₂ : Derived.{r, v} (R := R)} (fL : L₁ ⟶ L₂)
    [Has.{r, v} (R := R)] :
    (targetFunctor (R := R) K).map fL = map (R := R) (𝟙 K) fL := by
  simp only [targetFunctor, CochainComplex.Enriched.Over.RHom.targetFunctor,
    map, functor, CochainComplex.Enriched.Over.RHom.functor,
    DifferentialGradedCategory.HomComplex.Derived.RHom.targetFunctor_map,
    op_id]

/-- Identity morphisms act as the identity on carrier-polymorphic canonical `RHom`. -/
@[simp, stacks 0E1U "carrier-polymorphic RHom identity map"]
theorem map_id (K L : Derived.{r, v} (R := R)) [Has.{r, v} (R := R)] :
    map (R := R) (𝟙 K) (𝟙 L) = 𝟙 _ := by
  change (functor (R := R)).map
    (((𝟙 K).op, 𝟙 L) :
      (Opposite.op K, L) ⟶ (Opposite.op K, L)) = 𝟙 _
  exact (functor (R := R)).map_id (Opposite.op K, L)

/-- Carrier-polymorphic canonical `RHom` maps compose in both variables. -/
@[reassoc, stacks 0E1U "carrier-polymorphic RHom map composition"]
theorem map_comp
    {K₁ K₂ K₃ L₁ L₂ L₃ : Derived.{r, v} (R := R)}
    (fK₁ : K₂ ⟶ K₁) (fK₂ : K₃ ⟶ K₂)
    (fL₁ : L₁ ⟶ L₂) (fL₂ : L₂ ⟶ L₃) [Has.{r, v} (R := R)] :
    map (R := R) (fK₂ ≫ fK₁) (fL₁ ≫ fL₂) =
      map (R := R) fK₁ fL₁ ≫ map (R := R) fK₂ fL₂ := by
  change (functor (R := R)).map
      (((fK₂ ≫ fK₁).op, fL₁ ≫ fL₂) :
        (Opposite.op K₁, L₁) ⟶ (Opposite.op K₃, L₃)) =
    (functor (R := R)).map
        ((fK₁.op, fL₁) :
          (Opposite.op K₁, L₁) ⟶ (Opposite.op K₂, L₂)) ≫
      (functor (R := R)).map
        ((fK₂.op, fL₂) :
          (Opposite.op K₂, L₂) ⟶ (Opposite.op K₃, L₃))
  simpa only [op_comp, prod_comp] using
    (functor (R := R)).map_comp
      ((fK₁.op, fL₁) :
        (Opposite.op K₁, L₁) ⟶ (Opposite.op K₂, L₂))
      ((fK₂.op, fL₂) :
        (Opposite.op K₂, L₂) ⟶ (Opposite.op K₃, L₃))

/-- Carrier-polymorphic canonical `RHom` sends isomorphisms in both variables to an
isomorphism. -/
@[stacks 0E1U "carrier-polymorphic RHom map preserves isomorphisms"]
instance isIso_map
    {K₁ K₂ L₁ L₂ : Derived.{r, v} (R := R)}
    (fK : K₂ ⟶ K₁) (fL : L₁ ⟶ L₂)
    [Has.{r, v} (R := R)] [IsIso fK] [IsIso fL] :
    IsIso (map (R := R) fK fL) := by
  change IsIso ((functor (R := R)).map
    ((fK.op, fL) :
      (Opposite.op K₁, L₁) ⟶ (Opposite.op K₂, L₂)))
  letI : IsIso
      ((fK.op, fL) :
        (Opposite.op K₁, L₁) ⟶ (Opposite.op K₂, L₂)) :=
    (isIso_prod_iff (C := (Derived.{r, v} (R := R))ᵒᵖ)
      (D := Derived.{r, v} (R := R))).2 ⟨inferInstance, inferInstance⟩
  infer_instance

/-- The carrier-polymorphic canonical `RHom` map induced by two isomorphisms. -/
@[stacks 0E1U "carrier-polymorphic RHom functorial isomorphism"]
noncomputable abbrev mapIso
    {K₁ K₂ L₁ L₂ : Derived.{r, v} (R := R)}
    (eK : K₂ ≅ K₁) (eL : L₁ ≅ L₂) [Has.{r, v} (R := R)] :
    obj (R := R) K₁ L₁ ≅ obj (R := R) K₂ L₂ :=
  (functor (R := R)).mapIso (Iso.prod eK.op eL)

/-- The forward map of carrier-polymorphic `mapIso` is the canonical two-variable map. -/
@[simp, stacks 0E1U "carrier-polymorphic RHom functorial isomorphism forward map"]
theorem mapIso_hom
    {K₁ K₂ L₁ L₂ : Derived.{r, v} (R := R)}
    (eK : K₂ ≅ K₁) (eL : L₁ ≅ L₂) [Has.{r, v} (R := R)] :
    (mapIso (R := R) eK eL).hom = map (R := R) eK.hom eL.hom := rfl

/-- The inverse map of carrier-polymorphic `mapIso` is the canonical two-variable map. -/
@[simp, stacks 0E1U "carrier-polymorphic RHom functorial isomorphism inverse map"]
theorem mapIso_inv
    {K₁ K₂ L₁ L₂ : Derived.{r, v} (R := R)}
    (eK : K₂ ≅ K₁) (eL : L₁ ≅ L₂) [Has.{r, v} (R := R)] :
    (mapIso (R := R) eK eL).inv = map (R := R) eK.inv eL.inv := rfl

/-- The source component of carrier-polymorphic precomposition is the two-variable map. -/
@[simp, stacks 0E1U "carrier-polymorphic RHom precomposition component"]
theorem pre_app
    {K₁ K₂ : Derived.{r, v} (R := R)} (fK : K₂ ⟶ K₁)
    (L : Derived.{r, v} (R := R)) [Has.{r, v} (R := R)] :
    (pre (R := R) fK).app L = map (R := R) fK (𝟙 L) := rfl

/-- The target component of carrier-polymorphic postcomposition is the two-variable map. -/
@[simp, stacks 0E1U "carrier-polymorphic RHom postcomposition component"]
theorem post_app
    {L₁ L₂ : Derived.{r, v} (R := R)} (fL : L₁ ⟶ L₂)
    (K : Derived.{r, v} (R := R)) [Has.{r, v} (R := R)] :
    (post (R := R) fL).app (Opposite.op K) = map (R := R) (𝟙 K) fL := by
  simp only [post, curried, CochainComplex.Enriched.Over.RHom.curried,
    DifferentialGradedCategory.HomComplex.Derived.RHom.curried,
    CochainComplex.Enriched.Over.RHom.functor,
    Functor.flip_map_app, Functor.curry_obj_obj_map, map, functor, op_id]

/-- Precomposition by an identity source morphism is the identity natural transformation. -/
@[simp, stacks 0E1U "carrier-polymorphic RHom precomposition identity"]
theorem pre_id
    (K : Derived.{r, v} (R := R)) [Has.{r, v} (R := R)] :
    pre (R := R) (𝟙 K) = 𝟙 (targetFunctor (R := R) K) := by
  change (curried (R := R)).map ((𝟙 K).op) = 𝟙 _
  rw [op_id, Functor.map_id]

/-- Precomposition is contravariantly functorial in the source variable. -/
@[stacks 0E1U "carrier-polymorphic RHom precomposition composition"]
theorem pre_comp
    {K₁ K₂ K₃ : Derived.{r, v} (R := R)}
    (f : K₂ ⟶ K₁) (g : K₃ ⟶ K₂) [Has.{r, v} (R := R)] :
    pre (R := R) (g ≫ f) =
      pre (R := R) f ≫ pre (R := R) g := by
  change (curried (R := R)).map ((g ≫ f).op) =
    (curried (R := R)).map f.op ≫ (curried (R := R)).map g.op
  rw [op_comp, Functor.map_comp]

/-- Precomposition commutes with covariant maps in the target variable. -/
@[reassoc, stacks 0E1U "carrier-polymorphic RHom precomposition target naturality"]
theorem pre_naturality
    {K₁ K₂ : Derived.{r, v} (R := R)} (f : K₂ ⟶ K₁)
    {L₁ L₂ : Derived.{r, v} (R := R)} (g : L₁ ⟶ L₂)
    [Has.{r, v} (R := R)] :
    (pre (R := R) f).app L₁ ≫ map (R := R) (𝟙 K₂) g =
      map (R := R) (𝟙 K₁) g ≫ (pre (R := R) f).app L₂ := by
  simpa only [targetFunctor_map] using ((pre (R := R) f).naturality g).symm

/-- An explicit carrier-polymorphic canonical-`RHom` unit comparison and a source map induce a
natural transformation from the identity by precomposition. -/
@[stacks 0E1U "carrier-polymorphic canonical RHom unit induced by precomposition"]
noncomputable def unitOfPre
    {X U : Derived.{r, v} (R := R)}
    [Has.{r, v} (R := R)]
    (unitIso : targetFunctor (R := R) U ≅ 𝟭 (Derived.{r, v} (R := R)))
    (p : X ⟶ U) :
    𝟭 (Derived.{r, v} (R := R)) ⟶ targetFunctor (R := R) X :=
  unitIso.inv ≫ pre (R := R) p

/-- The component of the carrier-polymorphic canonical unit induced by precomposition. -/
@[simp, stacks 0E1U "carrier-polymorphic RHom precomposition unit component"]
theorem unitOfPre_app
    {X U : Derived.{r, v} (R := R)}
    [Has.{r, v} (R := R)]
    (unitIso : targetFunctor (R := R) U ≅ 𝟭 (Derived.{r, v} (R := R)))
    (p : X ⟶ U) (K : Derived.{r, v} (R := R)) :
    (unitOfPre unitIso p).app K =
      unitIso.inv.app K ≫ (pre (R := R) p).app K := rfl

/-- A carrier-polymorphic canonical `RHom` unit induced by precomposition is natural in the target
object. -/
@[reassoc, stacks 0E1U "carrier-polymorphic RHom precomposition unit naturality"]
theorem unitOfPre_naturality
    {X U K L : Derived.{r, v} (R := R)}
    [Has.{r, v} (R := R)]
    (unitIso : targetFunctor (R := R) U ≅ 𝟭 (Derived.{r, v} (R := R)))
    (p : X ⟶ U) (f : K ⟶ L) :
    f ≫ (unitOfPre unitIso p).app L =
      (unitOfPre unitIso p).app K ≫ (targetFunctor (R := R) X).map f := by
  simpa using (unitOfPre unitIso p).naturality f

/-- Precomposing the source map composes the induced carrier-polymorphic canonical unit with
canonical `RHom` precomposition. -/
@[stacks 0E1U "carrier-polymorphic RHom precomposition unit composition"]
theorem unitOfPre_comp
    {X Y U : Derived.{r, v} (R := R)}
    [Has.{r, v} (R := R)]
    (unitIso : targetFunctor (R := R) U ≅ 𝟭 (Derived.{r, v} (R := R)))
    (p : X ⟶ U) (q : Y ⟶ X) :
    unitOfPre unitIso (q ≫ p) =
      unitOfPre unitIso p ≫ pre (R := R) q := by
  simp only [unitOfPre, pre_comp, Category.assoc]

/-- The carrier-polymorphic canonical unit induced by an identity source map is the inverse unit
comparison. -/
@[simp, stacks 0E1U "carrier-polymorphic RHom precomposition unit identity"]
theorem unitOfPre_id
    (U : Derived.{r, v} (R := R))
    [Has.{r, v} (R := R)]
    (unitIso : targetFunctor (R := R) U ≅ 𝟭 (Derived.{r, v} (R := R))) :
    unitOfPre unitIso (𝟙 U) = unitIso.inv := by
  simp only [unitOfPre, pre_id, Category.comp_id]

end CategoryTheory.DerivedCategory.InternalHom.RHom.At
