module

public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.HomComplex.Derived.Over
public import ReasLib.Algebra.Homology.CochainComplex.ProjectiveResolution.FiniteProjective
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.At
import Mathlib.Tactic.CrossRefAttribute

/-!
# Canonical RHom models for derived internal Hom

Canonical derived enriched Hom is the root owner in this leaf.  Its object and universal map do
not depend on a chosen monoidal or closed structure on the derived category.  Projective-minus
computations are proposition-valued until a concrete inverse to that universal map is available;
no non-Prop isomorphism data is extracted from a deferred `IsIso` proof.

The optional closed bridge is separate.  It consumes an explicit ambient tensor model and an
explicit family of adjunctions identifying canonical `RHom(K, -)` as the right adjoint of canonical
fixed-right derived tensoring.  Only then is canonical `RHom` compared with the internal Hom
selected by an ordinary `MonoidalClosed` owner.

The generic enriched-Hom owner separates the universe of `A` from the carrier universe of
`ModuleCat A`.  This module facade is the standard same-universe convenience specialization
`ModuleCat.{v} A` (and its public `Has` abbreviation currently erases the carrier-universe
parameter); cross-universe consumers should use the carrier-polymorphic `RHom.At` facade (or the
generic `CochainComplex.Enriched.Over.RHom` owner).  No monoidal structure is needed here.

@stack 0E1U
-/

@[expose] public section

noncomputable section

universe r v

open CategoryTheory

namespace CategoryTheory.DerivedCategory.InternalHom.RHom

variable {A : Type r} [CommRing A]

/-- The existence condition for canonical two-variable derived enriched Hom of `A`-modules. -/
@[stacks 0E1U "canonical module RHom availability"]
abbrev Has : Prop :=
  CochainComplex.Enriched.Over.RHom.Has (R := A) (C := ModuleCat.{v} A)

/-- Canonical two-variable derived enriched Hom of `A`-modules. -/
@[stacks 0E1U "canonical module RHom bifunctor"]
noncomputable abbrev functor [Has (A := A)] :
    (DerivedCategory (ModuleCat.{v} A))ᵒᵖ × DerivedCategory (ModuleCat.{v} A) ⥤
      DerivedCategory (ModuleCat.{v} A) :=
  CochainComplex.Enriched.Over.RHom.functor (R := A) (C := ModuleCat.{v} A)

/- The curried and source-variable forms keep the contravariant input visible for downstream
  constructions that build towers of derived Hom objects. -/
/-- The canonical derived enriched Hom, curried in the target variable. -/
@[stacks 0E1U "curried canonical module RHom bifunctor"]
noncomputable abbrev curried [Has (A := A)] :
    (DerivedCategory (ModuleCat.{v} A))ᵒᵖ ⥤
      DerivedCategory (ModuleCat.{v} A) ⥤ DerivedCategory (ModuleCat.{v} A) :=
  CochainComplex.Enriched.Over.RHom.curried (R := A) (C := ModuleCat.{v} A)

/- The fixed-target form is the source-variable owner; it is intentionally separate from the
  target-variable `targetFunctor` so variance is never inferred from a coercion. -/
/-- The canonical derived `RHom(-, L)` functor in its contravariant source variable. -/
@[stacks 0E1U "source-variable canonical module RHom functor"]
noncomputable abbrev sourceFunctor
    (L : DerivedCategory (ModuleCat.{v} A)) [Has (A := A)] :
    (DerivedCategory (ModuleCat.{v} A))ᵒᵖ ⥤ DerivedCategory (ModuleCat.{v} A) :=
  CochainComplex.Enriched.Over.RHom.sourceFunctor
    (R := A) (C := ModuleCat.{v} A) L

/-- Canonical derived enriched Hom with its source object fixed. -/
@[stacks 0E1U "canonical module RHom target functor"]
noncomputable abbrev targetFunctor
    (K : DerivedCategory (ModuleCat.{v} A)) [Has (A := A)] :
    DerivedCategory (ModuleCat.{v} A) ⥤ DerivedCategory (ModuleCat.{v} A) :=
  CochainComplex.Enriched.Over.RHom.targetFunctor
    (R := A) (C := ModuleCat.{v} A) (Opposite.op K)

/-- The canonical derived internal-Hom object `RHom_A(K, L)`. -/
@[stacks 0E1U "canonical module RHom object"]
noncomputable abbrev obj
    (K L : DerivedCategory (ModuleCat.{v} A)) [Has (A := A)] :
    DerivedCategory (ModuleCat.{v} A) :=
  (targetFunctor (A := A) K).obj L

/-- The canonical map on `RHom`, contravariant in the source and covariant in the target. -/
@[stacks 0E1U "canonical module RHom map"]
noncomputable abbrev map
    {K₁ K₂ L₁ L₂ : DerivedCategory (ModuleCat.{v} A)}
    (fK : K₂ ⟶ K₁) (fL : L₁ ⟶ L₂) [Has (A := A)] :
    obj (A := A) K₁ L₁ ⟶ obj (A := A) K₂ L₂ :=
  (functor (A := A)).map (fK.op, fL)

/-- Precomposition on canonical `RHom`, packaged naturally in the target variable. -/
@[stacks 0E1U "canonical module RHom precomposition"]
noncomputable abbrev pre
    {K₁ K₂ : DerivedCategory (ModuleCat.{v} A)}
    (fK : K₂ ⟶ K₁) [Has (A := A)] :
    targetFunctor (A := A) K₁ ⟶ targetFunctor (A := A) K₂ :=
  (curried (A := A)).map fK.op

/-- Postcomposition on canonical `RHom`, packaged naturally in the source variable. -/
@[stacks 0E1U "canonical module RHom postcomposition"]
noncomputable abbrev post
    {L₁ L₂ : DerivedCategory (ModuleCat.{v} A)}
    (fL : L₁ ⟶ L₂) [Has (A := A)] :
    sourceFunctor (A := A) L₁ ⟶ sourceFunctor (A := A) L₂ :=
  (curried (A := A)).flip.map fL

/-- The component of canonical `RHom` precomposition is the corresponding two-variable map. -/
@[simp, stacks 0E1U "canonical module RHom precomposition component"]
theorem pre_app
    {K₁ K₂ : DerivedCategory (ModuleCat.{v} A)} (fK : K₂ ⟶ K₁)
    (L : DerivedCategory (ModuleCat.{v} A)) [Has (A := A)] :
    (pre (A := A) fK).app L = map (A := A) fK (𝟙 L) :=
  At.pre_app (R := A) fK L

/-- The component of canonical `RHom` postcomposition is the corresponding two-variable map. -/
@[simp, stacks 0E1U "canonical module RHom postcomposition component"]
theorem post_app
    {L₁ L₂ : DerivedCategory (ModuleCat.{v} A)} (fL : L₁ ⟶ L₂)
    (K : DerivedCategory (ModuleCat.{v} A)) [Has (A := A)] :
    (post (A := A) fL).app (Opposite.op K) = map (A := A) (𝟙 K) fL :=
  At.post_app (R := A) fL K

/-- Precomposition by an identity source morphism is the identity natural transformation. -/
@[simp, stacks 0E1U "canonical module RHom precomposition identity"]
theorem pre_id
    (K : DerivedCategory (ModuleCat.{v} A)) [Has (A := A)] :
    pre (A := A) (𝟙 K) = 𝟙 (targetFunctor (A := A) K) :=
  At.pre_id (R := A) K

/-- Precomposition is contravariantly functorial in the source variable. -/
@[stacks 0E1U "canonical module RHom precomposition composition"]
theorem pre_comp
    {K₁ K₂ K₃ : DerivedCategory (ModuleCat.{v} A)}
    (f : K₂ ⟶ K₁) (g : K₃ ⟶ K₂) [Has (A := A)] :
    pre (A := A) (g ≫ f) =
      pre (A := A) f ≫ pre (A := A) g :=
  At.pre_comp (R := A) f g

/-- Precomposition commutes with covariant maps in the target variable. -/
@[reassoc, stacks 0E1U "canonical module RHom precomposition target naturality"]
theorem pre_naturality
    {K₁ K₂ : DerivedCategory (ModuleCat.{v} A)} (f : K₂ ⟶ K₁)
    {L₁ L₂ : DerivedCategory (ModuleCat.{v} A)} (g : L₁ ⟶ L₂)
    [Has (A := A)] :
    (pre (A := A) f).app L₁ ≫ map (A := A) (𝟙 K₂) g =
      map (A := A) (𝟙 K₁) g ≫ (pre (A := A) f).app L₂ :=
  At.pre_naturality (R := A) f g

/-- An explicit canonical-`RHom` unit comparison and a map into its source induce a natural
transformation from the identity by canonical precomposition. -/
@[stacks 0E1U "canonical RHom unit induced by precomposition"]
noncomputable abbrev unitOfPre
    {X U : DerivedCategory (ModuleCat.{v} A)}
    [Has (A := A)]
    (unitIso : targetFunctor (A := A) U ≅
      𝟭 (DerivedCategory (ModuleCat.{v} A)))
    (p : X ⟶ U) :
    𝟭 (DerivedCategory (ModuleCat.{v} A)) ⟶ targetFunctor (A := A) X :=
  At.unitOfPre (R := A) unitIso p

/-- Objectwise, the canonical unit induced by `p` is the inverse explicit unit comparison
followed by canonical `RHom` precomposition along `p`. -/
@[simp, stacks 0E1U "canonical RHom precomposition unit component"]
theorem unitOfPre_app
    {X U : DerivedCategory (ModuleCat.{v} A)}
    [Has (A := A)]
    (unitIso : targetFunctor (A := A) U ≅
      𝟭 (DerivedCategory (ModuleCat.{v} A)))
    (p : X ⟶ U) (K : DerivedCategory (ModuleCat.{v} A)) :
    (unitOfPre unitIso p).app K =
      unitIso.inv.app K ≫ (pre (A := A) p).app K :=
  At.unitOfPre_app (R := A) unitIso p K

/-- A canonical `RHom` unit induced by precomposition is natural in its target object. -/
@[reassoc, stacks 0E1U "canonical RHom precomposition unit naturality"]
theorem unitOfPre_naturality
    {X U K L : DerivedCategory (ModuleCat.{v} A)}
    [Has (A := A)]
    (unitIso : targetFunctor (A := A) U ≅
      𝟭 (DerivedCategory (ModuleCat.{v} A)))
    (p : X ⟶ U) (f : K ⟶ L) :
    f ≫ (unitOfPre unitIso p).app L =
      (unitOfPre unitIso p).app K ≫ (targetFunctor (A := A) X).map f :=
  At.unitOfPre_naturality (R := A) unitIso p f

/-- Precomposing the source map composes the induced canonical unit with canonical `RHom`
precomposition. -/
@[stacks 0E1U "canonical RHom precomposition unit composition"]
theorem unitOfPre_comp
    {X Y U : DerivedCategory (ModuleCat.{v} A)}
    [Has (A := A)]
    (unitIso : targetFunctor (A := A) U ≅
      𝟭 (DerivedCategory (ModuleCat.{v} A)))
    (p : X ⟶ U) (q : Y ⟶ X) :
    unitOfPre unitIso (q ≫ p) =
      unitOfPre unitIso p ≫ pre (A := A) q :=
  At.unitOfPre_comp (R := A) unitIso p q

/-- The canonical unit induced by the identity of its source is the inverse explicit unit
comparison. -/
@[simp, stacks 0E1U "canonical RHom precomposition unit identity"]
theorem unitOfPre_id
    (U : DerivedCategory (ModuleCat.{v} A))
    [Has (A := A)]
    (unitIso : targetFunctor (A := A) U ≅
      𝟭 (DerivedCategory (ModuleCat.{v} A))) :
    unitOfPre unitIso (𝟙 U) = unitIso.inv :=
  At.unitOfPre_id (R := A) U unitIso

/-- The source-variable functor has the expected two-variable object formula. -/
@[simp, stacks 0E1U "canonical module RHom source functor object formula"]
theorem sourceFunctor_obj
    (K L : DerivedCategory (ModuleCat.{v} A)) [Has (A := A)] :
    (sourceFunctor (A := A) L).obj (Opposite.op K) = obj (A := A) K L :=
  At.sourceFunctor_obj (R := A) K L

/-- The target-variable functor has the expected two-variable object formula. -/
@[simp, stacks 0E1U "canonical module RHom target functor object formula"]
theorem targetFunctor_obj
    (K L : DerivedCategory (ModuleCat.{v} A)) [Has (A := A)] :
    (targetFunctor (A := A) K).obj L = obj (A := A) K L :=
  At.targetFunctor_obj (R := A) K L

/-- Source-variable maps are the first, contravariant components of the canonical `RHom` map. -/
@[simp, stacks 0E1U "canonical module RHom source functor map formula"]
theorem sourceFunctor_map
    {K₁ K₂ : DerivedCategory (ModuleCat.{v} A)} (fK : K₂ ⟶ K₁)
    (L : DerivedCategory (ModuleCat.{v} A)) [Has (A := A)] :
    (sourceFunctor (A := A) L).map fK.op = map (A := A) fK (𝟙 L) :=
  At.sourceFunctor_map (R := A) fK L

/-- Target-variable maps are the second, covariant components of the canonical `RHom` map. -/
@[simp, stacks 0E1U "canonical module RHom target functor map formula"]
theorem targetFunctor_map
    (K : DerivedCategory (ModuleCat.{v} A))
    {L₁ L₂ : DerivedCategory (ModuleCat.{v} A)} (fL : L₁ ⟶ L₂)
    [Has (A := A)] :
    (targetFunctor (A := A) K).map fL = map (A := A) (𝟙 K) fL :=
  At.targetFunctor_map (R := A) K fL

/-- Identity morphisms induce the identity map on canonical `RHom`. -/
@[simp, stacks 0E1U "canonical module RHom identity map"]
theorem map_id (K L : DerivedCategory (ModuleCat.{v} A)) [Has (A := A)] :
    map (A := A) (𝟙 K) (𝟙 L) = 𝟙 _ :=
  At.map_id (R := A) K L

/-- Canonical `RHom` maps compose contravariantly in the source and covariantly in the target. -/
@[reassoc, stacks 0E1U "canonical module RHom map composition"]
theorem map_comp
    {K₁ K₂ K₃ L₁ L₂ L₃ : DerivedCategory (ModuleCat.{v} A)}
    (fK₁ : K₂ ⟶ K₁) (fK₂ : K₃ ⟶ K₂)
    (fL₁ : L₁ ⟶ L₂) (fL₂ : L₂ ⟶ L₃) [Has (A := A)] :
    map (A := A) (fK₂ ≫ fK₁) (fL₁ ≫ fL₂) =
      map (A := A) fK₁ fL₁ ≫ map (A := A) fK₂ fL₂ :=
  At.map_comp (R := A) fK₁ fK₂ fL₁ fL₂

/-- Canonical `RHom` sends isomorphisms in both variables to an isomorphism. -/
@[stacks 0E1U "canonical module RHom map preserves isomorphisms"]
instance isIso_map
    {K₁ K₂ L₁ L₂ : DerivedCategory (ModuleCat.{v} A)}
    (fK : K₂ ⟶ K₁) (fL : L₁ ⟶ L₂)
    [Has (A := A)] [IsIso fK] [IsIso fL] :
    IsIso (map (A := A) fK fL) :=
  At.isIso_map (R := A) fK fL

/-- The canonical `RHom` map induced by isomorphisms, packaged as a concrete isomorphism. -/
@[stacks 0E1U "canonical module RHom functorial isomorphism"]
noncomputable abbrev mapIso
    {K₁ K₂ L₁ L₂ : DerivedCategory (ModuleCat.{v} A)}
    (eK : K₂ ≅ K₁) (eL : L₁ ≅ L₂) [Has (A := A)] :
    obj (A := A) K₁ L₁ ≅ obj (A := A) K₂ L₂ :=
  At.mapIso (R := A) eK eL

/-- The forward map of `mapIso` is the canonical map on the two forward morphisms. -/
@[simp, stacks 0E1U "canonical module RHom functorial isomorphism forward map"]
theorem mapIso_hom
    {K₁ K₂ L₁ L₂ : DerivedCategory (ModuleCat.{v} A)}
    (eK : K₂ ≅ K₁) (eL : L₁ ≅ L₂) [Has (A := A)] :
    (mapIso (A := A) eK eL).hom = map (A := A) eK.hom eL.hom :=
  At.mapIso_hom (R := A) eK eL

/-- The inverse of `mapIso` is the canonical map on the two inverse morphisms. -/
@[simp, stacks 0E1U "canonical module RHom functorial isomorphism inverse map"]
theorem mapIso_inv
    {K₁ K₂ L₁ L₂ : DerivedCategory (ModuleCat.{v} A)}
    (eK : K₂ ≅ K₁) (eL : L₁ ≅ L₂) [Has (A := A)] :
    (mapIso (A := A) eK eL).inv = map (A := A) eK.inv eL.inv :=
  At.mapIso_inv (R := A) eK eL

/-- The canonical derived-Hom universal map on a pair of strict module complexes. -/
@[stacks 0E1U "strict module component of canonical RHom"]
noncomputable abbrev unitApp
    (P F : CochainComplex (ModuleCat.{v} A) ℤ) [Has (A := A)] :
    DerivedCategory.Q.obj (CochainComplex.HomComplex.moduleComplex A P F) ⟶
      obj (A := A) (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj F) :=
  CochainComplex.Enriched.Over.RHom.unitApp
    (R := A) (C := ModuleCat.{v} A) P F

/-- A projective-minus source makes the strict Hom-complex comparison with canonical `RHom`
invertible. -/
@[stacks 0E1U "projective-minus computation of canonical module RHom"]
theorem unitApp_isIso_of_projectiveMinus
    (P : CochainComplex.ProjectiveMinus (ModuleCat.{v} A))
    (F : CochainComplex (ModuleCat.{v} A) ℤ) [Has (A := A)] :
    IsIso (unitApp (A := A) P F) := sorry

end CategoryTheory.DerivedCategory.InternalHom.RHom

namespace CochainComplex.ProjectiveMinus

open CategoryTheory

variable {A : Type r} [CommRing A]

/-- A projective-minus source Hom complex represents canonical `RHom` (Lemma 15.85.6, Stacks
`0E1U`). -/
@[stacks 0E1U, stacks 0A66 "projective-minus model for canonical RHom",
  stacks 0BYQ "Lemma 15.99.4 RHom model"]
theorem representsRHom
    (P : CochainComplex.ProjectiveMinus (ModuleCat.{v} A))
    (F : CochainComplex (ModuleCat.{v} A) ℤ)
    [CategoryTheory.DerivedCategory.InternalHom.RHom.Has (A := A)] :
    IsIsomorphic
      (DerivedCategory.Q.obj (CochainComplex.HomComplex.moduleComplex A P F))
      (CategoryTheory.DerivedCategory.InternalHom.RHom.obj
        (A := A) (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj F)) :=
  ⟨@asIso _ _ _ _
    (CategoryTheory.DerivedCategory.InternalHom.RHom.unitApp (A := A) P F)
    (CategoryTheory.DerivedCategory.InternalHom.RHom.unitApp_isIso_of_projectiveMinus P F)⟩

/-- A bounded-above termwise finite-projective source can be used directly to compute canonical
`RHom` (Lemma 15.85.6, Stacks `0E1U`). -/
@[stacks 0E1U, stacks 0A66 "finite-projective model for canonical RHom",
  stacks 0BYQ "Lemma 15.99.4 finite-projective RHom model"]
theorem representsRHom_of_finiteProjective
    (P F : CochainComplex (ModuleCat.{v} A) ℤ)
    (hP : CochainComplex.minus (ModuleCat.{v} A) P)
    (hPfp : P.IsTermwiseFiniteProjective)
    [CategoryTheory.DerivedCategory.InternalHom.RHom.Has (A := A)] :
    IsIsomorphic
      (DerivedCategory.Q.obj (CochainComplex.HomComplex.moduleComplex A P F))
      (CategoryTheory.DerivedCategory.InternalHom.RHom.obj
        (A := A) (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj F)) := by
  let P' : CochainComplex.ProjectiveMinus (ModuleCat.{v} A) :=
    ⟨⟨P, hP⟩, hPfp.projectiveObject⟩
  simpa only using representsRHom P' F

/-- The canonical `RHom` model computation transports across explicit representative
isomorphisms (Lemma 15.85.6, Stacks `0E1U`). -/
@[stacks 0E1U, stacks 0A66 "canonical RHom model after representative transport"]
theorem representsRHom_of_models
    {K L : DerivedCategory (ModuleCat.{v} A)}
    (P F : CochainComplex (ModuleCat.{v} A) ℤ)
    (eP : DerivedCategory.Q.obj P ≅ K) (eF : DerivedCategory.Q.obj F ≅ L)
    (hP : CochainComplex.minus (ModuleCat.{v} A) P)
    (hPfp : P.IsTermwiseFiniteProjective)
    [CategoryTheory.DerivedCategory.InternalHom.RHom.Has (A := A)] :
    IsIsomorphic
      (DerivedCategory.Q.obj (CochainComplex.HomComplex.moduleComplex A P F))
      (CategoryTheory.DerivedCategory.InternalHom.RHom.obj (A := A) K L) := by
  rcases representsRHom_of_finiteProjective P F hP hPfp with ⟨e⟩
  exact ⟨e ≪≫ CategoryTheory.DerivedCategory.InternalHom.RHom.mapIso
    (A := A) eP.symm eF⟩

end CochainComplex.ProjectiveMinus
