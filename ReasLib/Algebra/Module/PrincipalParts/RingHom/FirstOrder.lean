module

public import ReasLib.Algebra.Module.PrincipalParts.FirstOrder
public import ReasLib.Algebra.Module.PrincipalParts.RingHom

/-!
# The first principal-parts sequence for an explicit ring homomorphism

This file bundles the first-order principal-parts sequence in `ModuleCat`.  It is the reusable
algebraic owner for sectionwise presheaf and sheaf constructions: callers provide the ring map and
bundled module, without rebuilding source-ring actions or scalar towers.

@stack 09CN
-/

@[expose] public section

open CategoryTheory KaehlerDifferential

universe u

noncomputable section

namespace PrincipalParts.RingHom.FirstOrder

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The cotangent tensor module `Ω[S⁄R] ⊗[S] M` attached to an explicit ring map. -/
noncomputable abbrev cotangent (σ : R →+* S) (M : ModuleCat.{u} S) : ModuleCat.{u} S :=
  -- Local instance justification (instance diamond): relative differentials are specialized to
  -- this explicit `σ`, and another map `R →+* S` can induce a competing algebra structure.
  letI : Algebra R S := algebra σ
  ModuleCat.of S (TensorProduct S (Ω[S⁄R]) M)

/-- The bundled cotangent arrow into first principal parts. -/
@[stacks 09CN "explicit ring-hom cotangent arrow"]
noncomputable def cotangentTo (σ : R →+* S) (M : ModuleCat.{u} S) :
    cotangent σ M ⟶ PrincipalParts.RingHom.module σ M 1 :=
  -- Local instance justification (instance diamond): the presentation-level arrow requires the
  -- scalar action induced by this explicit `σ`, not a globally coherent endpoint instance.
  letI : Algebra R S := algebra σ
  letI : Module R M := sourceModule σ M
  letI : IsScalarTower R S M := IsScalarTower.of_compHom R S M
  ModuleCat.ofHom (PrincipalParts.FirstOrder.cotangentTo (R := R) (S := S) (M := M))

/-- The bundled projection from first principal parts to the original module. -/
@[stacks 09CN "explicit ring-hom first-order projection"]
noncomputable def projection (σ : R →+* S) (M : ModuleCat.{u} S) :
    PrincipalParts.RingHom.module σ M 1 ⟶ M :=
  -- Local instance justification (instance diamond): the projection is evaluated using the
  -- source action selected by the explicit map `σ` only for this adapter call.
  letI : Algebra R S := algebra σ
  letI : Module R M := sourceModule σ M
  letI : IsScalarTower R S M := IsScalarTower.of_compHom R S M
  ModuleCat.ofHom (PrincipalParts.FirstOrder.projection (R := R) (S := S) (M := M))

/-- The cotangent arrow followed by the first-order projection is zero. -/
theorem zero (σ : R →+* S) (M : ModuleCat.{u} S) :
    cotangentTo σ M ≫ projection σ M = 0 := sorry

/-- The first principal-parts short complex attached to an explicit ring map. -/
@[stacks 09CN "explicit ring-hom first-order sequence"]
noncomputable def sequence (σ : R →+* S) (M : ModuleCat.{u} S) :
    ShortComplex (ModuleCat.{u} S) :=
  ShortComplex.mk (cotangentTo σ M) (projection σ M) (zero σ M)

/-- The induced morphism on cotangent tensor modules. -/
noncomputable def cotangentMap (σ : R →+* S) {M N : ModuleCat.{u} S} (f : M ⟶ N) :
    cotangent σ M ⟶ cotangent σ N :=
  -- Local instance justification (instance diamond): the cotangent factor is formed relative to
  -- the explicit `σ`; maps with the same endpoints can define different relative objects.
  letI : Algebra R S := algebra σ
  ModuleCat.ofHom
    (TensorProduct.map (LinearMap.id : Ω[S⁄R] →ₗ[S] Ω[S⁄R]) f.hom)

/-- Cotangent tensor functoriality preserves identity morphisms. -/
@[simp]
theorem cotangentMap_id (σ : R →+* S) (M : ModuleCat.{u} S) :
    cotangentMap σ (𝟙 M) = 𝟙 (cotangent σ M) := sorry

/-- Cotangent tensor functoriality preserves composition. -/
@[simp]
theorem cotangentMap_comp (σ : R →+* S) {M N P : ModuleCat.{u} S}
    (f : M ⟶ N) (g : N ⟶ P) :
    cotangentMap σ (f ≫ g) = cotangentMap σ f ≫ cotangentMap σ g := sorry

/-- Tensoring with relative Kähler differentials defines an endofunctor on bundled target-ring
modules. -/
noncomputable def cotangentFunctor (σ : R →+* S) : ModuleCat.{u} S ⥤ ModuleCat.{u} S where
  obj M := cotangent σ M
  map f := cotangentMap σ f
  map_id M := cotangentMap_id σ M
  map_comp f g := cotangentMap_comp σ f g

/-- The cotangent arrow is natural in the bundled module. -/
theorem cotangentTo_naturality (σ : R →+* S) {M N : ModuleCat.{u} S} (f : M ⟶ N) :
    cotangentMap σ f ≫ cotangentTo σ N =
      cotangentTo σ M ≫ PrincipalParts.RingHom.map σ 1 f := sorry

/-- The first-order projection is natural in the bundled module. -/
theorem projection_naturality (σ : R →+* S) {M N : ModuleCat.{u} S} (f : M ⟶ N) :
    PrincipalParts.RingHom.map σ 1 f ≫ projection σ N = projection σ M ≫ f := sorry

/-- The cotangent arrows form a natural transformation into first principal parts. -/
noncomputable def cotangentToNatTrans (σ : R →+* S) :
    cotangentFunctor σ ⟶ PrincipalParts.RingHom.functor σ 1 where
  app M := cotangentTo σ M
  naturality _ _ f := cotangentTo_naturality σ f

/-- The first-order projections form a natural transformation to the identity functor. -/
noncomputable def projectionNatTrans (σ : R →+* S) :
    PrincipalParts.RingHom.functor σ 1 ⟶ 𝟭 (ModuleCat.{u} S) where
  app M := projection σ M
  naturality _ _ f := projection_naturality σ f

/-- The morphism of first principal-parts short complexes induced by a bundled module morphism. -/
noncomputable def sequenceMap (σ : R →+* S) {M N : ModuleCat.{u} S} (f : M ⟶ N) :
    sequence σ M ⟶ sequence σ N :=
  ShortComplex.Hom.mk (cotangentMap σ f) (PrincipalParts.RingHom.map σ 1 f) f
    (cotangentTo_naturality σ f) (projection_naturality σ f)

/-- The first principal-parts sequence map preserves identity morphisms. -/
@[simp]
theorem sequenceMap_id (σ : R →+* S) (M : ModuleCat.{u} S) :
    sequenceMap σ (𝟙 M) = 𝟙 (sequence σ M) := sorry

/-- The first principal-parts sequence map preserves composition. -/
@[simp]
theorem sequenceMap_comp (σ : R →+* S) {M N P : ModuleCat.{u} S}
    (f : M ⟶ N) (g : N ⟶ P) :
    sequenceMap σ (f ≫ g) = sequenceMap σ f ≫ sequenceMap σ g := sorry

/-- The first principal-parts short complex is functorial in the bundled target-ring module. -/
@[stacks 09CN "explicit ring-hom first principal-parts sequence functor"]
noncomputable def sequenceFunctor (σ : R →+* S) :
    ModuleCat.{u} S ⥤ ShortComplex (ModuleCat.{u} S) where
  obj M := sequence σ M
  map f := sequenceMap σ f
  map_id M := sequenceMap_id σ M
  map_comp f g := sequenceMap_comp σ f g

/-- The explicit-ring-hom first principal-parts sequence is short exact. -/
@[stacks 09CN "explicit ring-hom first-order short exactness"]
theorem shortExact (σ : R →+* S) (M : ModuleCat.{u} S) :
    (sequence σ M).ShortExact := sorry

end PrincipalParts.RingHom.FirstOrder

end
