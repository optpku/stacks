module

public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.At
public import ReasLib.CategoryTheory.Monoidal.Closed.PullbackComparison.Natural
public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.BraidedClosed
import Mathlib.Tactic.CrossRefAttribute

/-!
# Carrier-polymorphic bifunctor comparison for canonical module RHom

This is the universe-polymorphic owner for a coherent identification of canonical module `RHom`
with a selected internal-Hom bifunctor.  The module carrier universe remains explicit, which is
needed when change-of-rings functors enlarge it.  The aligned-universe convenience API remains in
`RHom.Closed.Bifunctor`.
@stack 0E1U
-/

@[expose] public section

noncomputable section

universe r v

open CategoryTheory
open CategoryTheory.MonoidalClosed

namespace CategoryTheory.DerivedCategory.InternalHom.RHom.At

variable {R : Type r} [CommRing R]
variable [MonoidalCategory (Derived.{r, v} (R := R))]

/-- 0E1U: A selected closed structure together with a two-variable identification of
carrier-polymorphic canonical module `RHom` and its internal-Hom bifunctor. -/
@[stacks 0E1U "carrier-polymorphic bifunctor comparison for canonical module RHom"]
structure BifunctorComparison [Has.{r, v} (R := R)] where
  /-- The selected closed structure. -/
  closed : MonoidalClosed (Derived.{r, v} (R := R))
  /-- The comparison, natural in the contravariant source and covariant target variables. -/
  functorIso : functor (R := R) ≅
    Functor.PullbackInternalHom.Bifunctor.internalHomFunctor closed

/-- `0E1U:` A coherent ambient right-tensor adjunction for carrier-polymorphic canonical
`RHom`.  Unlike a family of pointwise adjunctions, this retains naturality in the tensor factor. -/
@[stacks 0E1U "carrier-polymorphic parametrized tensor-RHom adjunction"]
abbrev TensorAdjunction₂ [Has.{r, v} (R := R)] :=
  MonoidalCategory.tensoringRight (Derived.{r, v} (R := R)) ⊣₂ curried (R := R)

/-- `0E1U:` Canonical `RHom` as a right internal-Hom owner from a genuine parametrized tensor
adjunction. -/
@[stacks 0E1U "carrier-polymorphic canonical RHom right internal-Hom owner"]
noncomputable def rightInternalHomOf [Has.{r, v} (R := R)]
    (adj₂ : TensorAdjunction₂ (R := R)) :
    RightInternalHom (Derived.{r, v} (R := R)) where
  hom := curried (R := R)
  adj₂ := adj₂

/-- `0E1U:` Package an explicit coherent comparison between canonical `RHom` and a selected
closed internal-Hom bifunctor.  The natural isomorphism is an input; pointwise uniqueness alone does
not manufacture it. -/
@[stacks 0E1U "construct carrier-polymorphic RHom bifunctor comparison from explicit iso"]
noncomputable def BifunctorComparison.ofIso
    (H : MonoidalClosed (Derived.{r, v} (R := R)))
    [Has.{r, v} (R := R)]
    (e : functor (R := R) ≅
      @Functor.PullbackInternalHom.Bifunctor.internalHomFunctor
        (Derived.{r, v} (R := R)) _ _ H) :
    BifunctorComparison (R := R) :=
  { closed := H
    functorIso := e }

section Braided

variable [BraidedCategory (Derived.{r, v} (R := R))]

/-- `0E1U:` The canonical coherent bifunctor isomorphism obtained from a parametrized
tensor-`RHom` adjunction and a selected closed structure. -/
@[stacks 0E1U "RHom bifunctor isomorphism from parametrized adjunction"]
noncomputable def bifunctorIsoOfAdjunction [Has.{r, v} (R := R)]
    (H : MonoidalClosed (Derived.{r, v} (R := R)))
    (adj₂ : TensorAdjunction₂ (R := R)) :
    functor (R := R) ≅
      Functor.PullbackInternalHom.Bifunctor.internalHomFunctor H :=
  (eqToIso (Functor.uncurry_obj_curry_obj (functor (R := R)))).symm ≪≫
    Functor.uncurry.mapIso
      ((rightInternalHomOf adj₂).uniqueIso (RightInternalHom.ofBraidedClosedOf H)) ≪≫
    Functor.uncurry.mapIso
      (eqToIso (RightInternalHom.ofBraidedClosedOf_hom H))

/-- `0E1U:` Construct the coherent comparison with a selected closed structure from a genuine
parametrized tensor-`RHom` adjunction.  The bifunctor isomorphism is the canonical uniqueness
isomorphism of right internal Homs. -/
@[stacks 0E1U "RHom bifunctor comparison from parametrized adjunction"]
noncomputable def BifunctorComparison.ofAdjunction [Has.{r, v} (R := R)]
    (H : MonoidalClosed (Derived.{r, v} (R := R)))
    (adj₂ : TensorAdjunction₂ (R := R)) :
    BifunctorComparison (R := R) :=
  BifunctorComparison.ofIso H (bifunctorIsoOfAdjunction H adj₂)

/-- `0E1U:` The comparison constructed from a parametrized adjunction carries the canonical
right-internal-Hom uniqueness isomorphism. -/
@[simp, stacks 0E1U "parametrized RHom comparison functor isomorphism"]
theorem BifunctorComparison.ofAdjunction_functorIso [Has.{r, v} (R := R)]
    (H : MonoidalClosed (Derived.{r, v} (R := R)))
    (adj₂ : TensorAdjunction₂ (R := R)) :
    (BifunctorComparison.ofAdjunction H adj₂).functorIso =
      bifunctorIsoOfAdjunction H adj₂ := rfl

end Braided

namespace BifunctorComparison

variable [Has.{r, v} (R := R)]

/-- 0E1U: The objectwise component of a carrier-polymorphic canonical-`RHom` comparison. -/
@[stacks 0E1U "carrier-polymorphic bifunctor comparison object isomorphism"]
noncomputable abbrev objIso
    (M : BifunctorComparison (R := R))
    (K L : Derived.{r, v} (R := R)) :
    obj (R := R) K L ≅ (ihomOf M.closed K).obj L :=
  M.functorIso.app (Opposite.op K, L)

/-- 0E1U: Contravariant source naturality of a carrier-polymorphic canonical-`RHom` comparison. -/
@[reassoc, stacks 0E1U "carrier-polymorphic bifunctor comparison source naturality"]
theorem objIso_natural_source
    (M : BifunctorComparison (R := R))
    {K₁ K₂ : Derived.{r, v} (R := R)} (f : K₂ ⟶ K₁)
    (L : Derived.{r, v} (R := R)) :
    map (R := R) f (𝟙 L) ≫ (M.objIso K₂ L).hom =
      (M.objIso K₁ L).hom ≫ (preOf M.closed f).app L := by
  change (functor (R := R)).map (f.op, 𝟙 L) ≫
      M.functorIso.hom.app (Opposite.op K₂, L) =
    M.functorIso.hom.app (Opposite.op K₁, L) ≫ (preOf M.closed f).app L
  simpa only [Functor.PullbackInternalHom.Bifunctor.internalHomFunctor,
    MonoidalClosed.internalHomOf, MonoidalClosed.internalHom, MonoidalClosed.preOf,
    Functor.uncurry_obj_map, Functor.map_id, NatTrans.id_app,
    Quiver.Hom.unop_op, Category.comp_id] using! M.functorIso.hom.naturality
      ((f.op, 𝟙 L) : (Opposite.op K₁, L) ⟶ (Opposite.op K₂, L))

/-- 0E1U: Covariant target naturality of a carrier-polymorphic canonical-`RHom` comparison. -/
@[reassoc, stacks 0E1U "carrier-polymorphic bifunctor comparison target naturality"]
theorem objIso_natural_target
    (M : BifunctorComparison (R := R))
    (K : Derived.{r, v} (R := R))
    {L₁ L₂ : Derived.{r, v} (R := R)} (f : L₁ ⟶ L₂) :
    map (R := R) (𝟙 K) f ≫ (M.objIso K L₂).hom =
      (M.objIso K L₁).hom ≫ (ihomOf M.closed K).map f := by
  change (functor (R := R)).map (𝟙 (Opposite.op K), f) ≫
      M.functorIso.hom.app (Opposite.op K, L₂) =
    M.functorIso.hom.app (Opposite.op K, L₁) ≫ (ihomOf M.closed K).map f
  simpa only [Functor.PullbackInternalHom.Bifunctor.internalHomFunctor,
    MonoidalClosed.internalHomOf, MonoidalClosed.internalHom, MonoidalClosed.ihomOf,
    Functor.uncurry_obj_map, Functor.map_id, NatTrans.id_app, unop_id,
    MonoidalClosed.pre_id, Category.id_comp] using! M.functorIso.hom.naturality
      ((𝟙 (Opposite.op K), f) : (Opposite.op K, L₁) ⟶ (Opposite.op K, L₂))

/-- The fixed-target comparison is natural in the contravariant source variable. -/
@[reassoc, stacks 0E1U "carrier-polymorphic fixed-target RHom naturality"]
theorem sourceIso_naturality
    (M : BifunctorComparison (R := R))
    {K₁ K₂ : Derived.{r, v} (R := R)} (f : K₂ ⟶ K₁)
    (L : Derived.{r, v} (R := R)) :
    (sourceFunctor (R := R) L).map f.op ≫ (M.objIso K₂ L).hom =
      (M.objIso K₁ L).hom ≫
        ((MonoidalClosed.internalHomOf M.closed).flip.obj L).map f.op := by
  simpa only [sourceFunctor_map, MonoidalClosed.sourceFunctorOf_map] using!
    M.objIso_natural_source f L

/-- The inverse fixed-target comparison is natural in the contravariant source variable. -/
@[reassoc, stacks 0E1U "inverse carrier-polymorphic fixed-target naturality"]
theorem sourceIso_inv_naturality
    (M : BifunctorComparison (R := R))
    {K₁ K₂ : Derived.{r, v} (R := R)} (f : K₂ ⟶ K₁)
    (L : Derived.{r, v} (R := R)) :
    ((MonoidalClosed.internalHomOf M.closed).flip.obj L).map f.op ≫
        (M.objIso K₂ L).inv =
      (M.objIso K₁ L).inv ≫ (sourceFunctor (R := R) L).map f.op := by
  rw [MonoidalClosed.sourceFunctorOf_map, sourceFunctor_map]
  change (preOf M.closed f).app L ≫
      M.functorIso.inv.app (Opposite.op K₂, L) =
    M.functorIso.inv.app (Opposite.op K₁, L) ≫
      (functor (R := R)).map (f.op, 𝟙 L)
  simpa only [Functor.PullbackInternalHom.Bifunctor.internalHomFunctor,
    MonoidalClosed.internalHomOf, MonoidalClosed.internalHom, MonoidalClosed.preOf,
    Functor.uncurry_obj_map, Functor.map_id, NatTrans.id_app,
    Quiver.Hom.unop_op, Category.comp_id] using! M.functorIso.inv.naturality
      ((f.op, 𝟙 L) : (Opposite.op K₁, L) ⟶ (Opposite.op K₂, L))

/-- The fixed-target comparison assembled as a natural isomorphism of source-variable functors. -/
noncomputable def sourceIso
    (M : BifunctorComparison (R := R))
    (L : Derived.{r, v} (R := R)) :
    sourceFunctor (R := R) L ≅
      (MonoidalClosed.internalHomOf M.closed).flip.obj L :=
  NatIso.ofComponents
    (fun X => M.objIso X.unop L)
    (fun {_ _} f => sourceIso_naturality M f.unop L)

/-- The forward component of the fixed-target comparison is the objectwise comparison. -/
@[simp, stacks 0E1U "fixed-target RHom comparison component"]
theorem sourceIso_hom_app
    (M : BifunctorComparison (R := R))
    (K L : Derived.{r, v} (R := R)) :
    (M.sourceIso L).hom.app (Opposite.op K) = (M.objIso K L).hom := rfl

/-- The inverse component of the fixed-target comparison is the inverse objectwise comparison. -/
@[simp, stacks 0E1U "inverse fixed-target RHom comparison component"]
theorem sourceIso_inv_app
    (M : BifunctorComparison (R := R))
    (K L : Derived.{r, v} (R := R)) :
    (M.sourceIso L).inv.app (Opposite.op K) = (M.objIso K L).inv := rfl

/-- The fixed-source comparison is natural in the covariant target variable. -/
@[reassoc, stacks 0E1U "carrier-polymorphic fixed-source RHom naturality"]
theorem targetIso_naturality
    (M : BifunctorComparison (R := R))
    (K : Derived.{r, v} (R := R))
    {L₁ L₂ : Derived.{r, v} (R := R)} (f : L₁ ⟶ L₂) :
    (targetFunctor (R := R) K).map f ≫ (M.objIso K L₂).hom =
      (M.objIso K L₁).hom ≫ (MonoidalClosed.ihomOf M.closed K).map f := by
  simpa only [targetFunctor_map] using M.objIso_natural_target K f

/-- The inverse fixed-source comparison is natural in the covariant target variable. -/
@[reassoc, stacks 0E1U "inverse carrier-polymorphic fixed-source RHom naturality"]
theorem targetIso_inv_naturality
    (M : BifunctorComparison (R := R))
    (K : Derived.{r, v} (R := R))
    {L₁ L₂ : Derived.{r, v} (R := R)} (f : L₁ ⟶ L₂) :
    (MonoidalClosed.ihomOf M.closed K).map f ≫ (M.objIso K L₂).inv =
      (M.objIso K L₁).inv ≫ (targetFunctor (R := R) K).map f := by
  rw [targetFunctor_map]
  change (ihomOf M.closed K).map f ≫
      M.functorIso.inv.app (Opposite.op K, L₂) =
    M.functorIso.inv.app (Opposite.op K, L₁) ≫
      (functor (R := R)).map (𝟙 (Opposite.op K), f)
  simpa only [Functor.PullbackInternalHom.Bifunctor.internalHomFunctor,
    MonoidalClosed.internalHomOf, MonoidalClosed.internalHom, MonoidalClosed.ihomOf,
    Functor.uncurry_obj_map, Functor.map_id, NatTrans.id_app, unop_id,
    MonoidalClosed.pre_id, Category.id_comp] using! M.functorIso.inv.naturality
      ((𝟙 (Opposite.op K), f) : (Opposite.op K, L₁) ⟶ (Opposite.op K, L₂))

/-- The fixed-source comparison assembled as a natural isomorphism of target-variable functors. -/
noncomputable def targetIso
    (M : BifunctorComparison (R := R))
    (K : Derived.{r, v} (R := R)) :
    targetFunctor (R := R) K ≅ MonoidalClosed.ihomOf M.closed K :=
  NatIso.ofComponents (M.objIso K)
    (fun {_ _} f => targetIso_naturality M K f)

/-- The forward component of the fixed-source comparison is the objectwise comparison. -/
@[simp, stacks 0E1U "fixed-source RHom comparison component"]
theorem targetIso_hom_app
    (M : BifunctorComparison (R := R))
    (K L : Derived.{r, v} (R := R)) :
    (M.targetIso K).hom.app L = (M.objIso K L).hom := rfl

/-- The inverse component of the fixed-source comparison is the inverse objectwise comparison. -/
@[simp, stacks 0E1U "inverse fixed-source RHom comparison component"]
theorem targetIso_inv_app
    (M : BifunctorComparison (R := R))
    (K L : Derived.{r, v} (R := R)) :
    (M.targetIso K).inv.app L = (M.objIso K L).inv := rfl

end BifunctorComparison

end CategoryTheory.DerivedCategory.InternalHom.RHom.At
