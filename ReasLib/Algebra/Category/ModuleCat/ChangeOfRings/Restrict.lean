/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.Submodule.RestrictScalars
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Scalar structures and identity comparisons for restriction of scalars

This leaf owns the scalar compatibility retained by restriction of scalars and
the standard comparison between a module carrying compatible `R`- and
`S`-module structures and the result of restricting its `S`-scalar structure
along `R → S`.  It is independent of any particular algebraic construction
using those facts.
-/

@[expose] public section

open CategoryTheory

universe u v w x

noncomputable section

namespace ModuleCat.RestrictScalars

section Submodule

variable {R : Type u} {S : Type v} [Ring R] [Ring S]

/-- Closure of an `S`-submodule under the `R`-action supplied by restriction along
`f : R →+* S`. -/
theorem submodule_smul_mem (f : R →+* S) (M : ModuleCat.{w} S)
    (P : Submodule S M) (r : R) {x : M} (hx : x ∈ P) :
    f r • x ∈ P :=
  P.smul_mem (f r) hx

/-- An `S`-submodule, regarded canonically as an `R`-submodule after restriction of scalars
along `f`. -/
@[stacks 09CI "restriction-of-scalars submodule"]
def submodule (f : R →+* S) (M : ModuleCat.{w} S) (P : Submodule S M) :
    Submodule R ((ModuleCat.restrictScalars f).obj M) where
  carrier := {x | x ∈ P}
  zero_mem' := P.zero_mem
  add_mem' := P.add_mem
  smul_mem' := submodule_smul_mem f M P

/-- Membership is unchanged by bundled restriction of scalars. -/
@[simp]
theorem mem_submodule_iff (f : R →+* S) (M : ModuleCat.{w} S)
    (P : Submodule S M) (x : (ModuleCat.restrictScalars f).obj M) :
    x ∈ submodule f M P ↔ x ∈ P :=
  Iff.rfl

/-- The module carried by a submodule, restricted along the same ring homomorphism as its
ambient module. -/
@[stacks 09CI "restriction-of-scalars submodule object"]
abbrev submoduleObj (f : R →+* S) (M : ModuleCat.{w} S)
    (P : Submodule S M) : ModuleCat.{w} R :=
  (ModuleCat.restrictScalars f).obj (ModuleCat.of S P)

/-- The inclusion of a submodule after restricting both its source and target scalars. -/
@[stacks 09CI "restriction-of-scalars submodule inclusion"]
def submoduleSubtype (f : R →+* S) (M : ModuleCat.{w} S)
    (P : Submodule S M) :
    submoduleObj f M P ⟶ (ModuleCat.restrictScalars f).obj M :=
  (ModuleCat.restrictScalars f).map (ModuleCat.ofHom P.subtype)

/-- The restricted inclusion has the expected restricted submodule as its range. -/
theorem range_submoduleSubtype (f : R →+* S) (M : ModuleCat.{w} S)
    (P : Submodule S M) :
    LinearMap.range (submoduleSubtype f M P).hom = submodule f M P := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- Restriction of scalars commutes with taking the range of a module morphism. -/
@[stacks 09CI "restriction-of-scalars range"]
theorem submodule_range (f : R →+* S) {M N : ModuleCat.{w} S} (g : M ⟶ N) :
    submodule f N (LinearMap.range g.hom) =
      LinearMap.range ((ModuleCat.restrictScalars f).map g).hom := by
  ext x
  rfl

end Submodule

namespace Surjective

variable {R : Type u} {S : Type v} [Ring R] [Ring S]

/-- An `R`-linear map between `S`-modules is `S`-linear when the scalar map `R →+* S` is
surjective. -/
theorem map_smul (f : R →+* S) (hf : Function.Surjective f)
    {M N : ModuleCat.{w} S}
    (g : (ModuleCat.restrictScalars f).obj M ⟶ (ModuleCat.restrictScalars f).obj N)
    (s : S) (m : M) : g (s • m) = s • g m := by
  obtain ⟨r, rfl⟩ := hf s
  exact g.hom.map_smul r m

/-- Recover the unique `S`-linear map underlying an `R`-linear map between modules restricted
along a surjective ring homomorphism. -/
def preimage (f : R →+* S) (hf : Function.Surjective f)
    {M N : ModuleCat.{w} S}
    (g : (ModuleCat.restrictScalars f).obj M ⟶ (ModuleCat.restrictScalars f).obj N) : M ⟶ N :=
  ModuleCat.ofHom
    { toFun := g
      map_add' := g.hom.map_add
      map_smul' := map_smul f hf g }

/-- Restricting the recovered `S`-linear map gives the original `R`-linear map. -/
theorem map_preimage (f : R →+* S) (hf : Function.Surjective f)
    {M N : ModuleCat.{w} S}
    (g : (ModuleCat.restrictScalars f).obj M ⟶ (ModuleCat.restrictScalars f).obj N) :
    (ModuleCat.restrictScalars f).map (preimage f hf g) = g := by
  apply ModuleCat.hom_ext
  rfl

/-- Recovering an `S`-linear map after restricting it leaves the map unchanged. -/
theorem preimage_map (f : R →+* S) (hf : Function.Surjective f)
    {M N : ModuleCat.{w} S} (g : M ⟶ N) :
    preimage f hf ((ModuleCat.restrictScalars f).map g) = g := by
  apply ModuleCat.hom_ext
  rfl

/-- Restriction of scalars along a surjective ring homomorphism is fully faithful. -/
@[stacks 05CR "surjective restriction"]
def fullyFaithful (f : R →+* S) (hf : Function.Surjective f) :
    (ModuleCat.restrictScalars f).FullyFaithful where
  preimage := preimage f hf
  map_preimage := map_preimage f hf
  preimage_map := preimage_map f hf

end Surjective

section SurjectiveClass

variable {R : Type u} {S : Type v} [Ring R] [Ring S]

/-- Restriction of scalars along a ring homomorphism carrying the canonical surjectivity
typeclass is fully faithful. -/
@[stacks 05CR "surjective restriction"]
def fullyFaithful (f : R →+* S) [RingHomSurjective f] :
    (ModuleCat.restrictScalars f).FullyFaithful :=
  Surjective.fullyFaithful f f.surjective

/-- Restriction of scalars along a surjective ring homomorphism is full. -/
@[stacks 05CR "surjective restriction full"]
instance full (f : R →+* S) [RingHomSurjective f] :
    (ModuleCat.restrictScalars f).Full :=
  (fullyFaithful f).full

end SurjectiveClass

section AlgebraMap

variable {R₀ : Type u} {S₀ : Type v} [CommRing R₀] [Ring S₀] [Algebra R₀ S₀]

/-- Restriction of scalars along an algebra map retains the canonical scalar-tower
compatibility with the original module action. -/
@[stacks 09CI "restriction-of-scalars scalar tower"]
instance isScalarTower (M : ModuleCat.{w} S₀) :
    IsScalarTower R₀ S₀
      ((ModuleCat.restrictScalars (algebraMap R₀ S₀)).obj M) :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- The raw carrier of an `S₀`-module inherits the `R₀`-module structure from
the bundled restriction-of-scalars object. This bridge keeps the underlying module type while
retaining the restricted scalar action. -/
@[stacks 09CI "raw-carrier restriction-of-scalars module"]
instance (priority := 100) rawModule (M : ModuleCat.{w} S₀) : Module R₀ M :=
  ((ModuleCat.restrictScalars (algebraMap R₀ S₀)).obj M).isModule

/-- The scalar tower on the raw carrier is the bundled restriction tower. -/
@[stacks 09CI "raw-carrier restriction-of-scalars scalar tower"]
instance (priority := 100) rawIsScalarTower (M : ModuleCat.{w} S₀) : IsScalarTower R₀ S₀ M :=
  ModuleCat.RestrictScalars.isScalarTower M

namespace AlgebraMap

/-- Mathlib's scalar-tower restriction of an `S₀`-submodule, bundled without requiring a local
`R₀`-module instance on the original carrier. -/
@[stacks 09CI "algebra-map restricted submodule"]
noncomputable def submodule (M : ModuleCat.{w} S₀) (P : Submodule S₀ M) :
    Submodule R₀ ((ModuleCat.restrictScalars (algebraMap R₀ S₀)).obj M) :=
  @Submodule.restrictScalars R₀ S₀ M inferInstance
    M.isAddCommGroup.toAddCommMonoid inferInstance
    ((ModuleCat.restrictScalars (algebraMap R₀ S₀)).obj M).isModule M.isModule
    inferInstance
    (ModuleCat.RestrictScalars.isScalarTower (R₀ := R₀) (S₀ := S₀) M) P

end AlgebraMap

/-- For an algebra map, the bundled restricted submodule agrees with mathlib's
`Submodule.restrictScalars`. -/
theorem submodule_algebraMap (M : ModuleCat.{w} S₀) (P : Submodule S₀ M) :
    submodule (algebraMap R₀ S₀) M P =
      AlgebraMap.submodule M P := by
  ext x
  rfl

end AlgebraMap

section Commutative

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The original `S`-action on an `S`-module commutes with the `R`-action
obtained by restricting scalars along `f : R →+* S`. -/
@[stacks 09CI "restriction-of-scalars scalar commutation"]
instance smulCommClass (f : R →+* S) (M : ModuleCat.{w} S) :
    SMulCommClass S R ((ModuleCat.restrictScalars f).obj M) where
  smul_comm s r m := by
    change s • (f r • m) = f r • (s • m)
    exact smul_comm s (f r) m

/-- The restricted `R`-action commutes canonically with the retained `S`-action. This orientation
supplies the `S`-module structure on spaces of `R`-linear maps. -/
@[stacks 09CI "restriction-of-scalars reverse scalar commutation"]
instance baseSmulCommClass (f : R →+* S) (M : ModuleCat.{w} S) :
    SMulCommClass R S ((ModuleCat.restrictScalars f).obj M) where
  smul_comm r s m := by
    change f r • (s • m) = s • (f r • m)
    exact smul_comm (f r) s m

/-- Every `S`-linear map between modules restricted along the same ring homomorphism is
compatible with the retained `R`-actions.  This is the map-indexed instance used by generic
restriction-of-scalars constructions such as postcomposition of differential operators. -/
@[stacks 09CI "restriction-of-scalars linear compatibility"]
instance compatibleSMul (f : R →+* S) (M N : ModuleCat.{w} S) :
    LinearMap.CompatibleSMul ((ModuleCat.restrictScalars f).obj M)
      ((ModuleCat.restrictScalars f).obj N) R S where
  map_smul g r m := by
    change g (f r • m) = f r • g m
    exact g.map_smul (f r) m

section Composition

variable {T : Type w} [CommRing T]

/-- Compose module morphisms lying over two successive ring homomorphisms, identifying iterated
restriction of scalars with restriction along the composite. -/
@[stacks 09CP "composition under scalar restriction"]
noncomputable def homComp (f : R →+* S) (g : S →+* T)
    {M₀ : ModuleCat.{x} R} {M₁ : ModuleCat.{x} S} {M₂ : ModuleCat.{x} T}
    (α : M₀ ⟶ (ModuleCat.restrictScalars f).obj M₁)
    (β : M₁ ⟶ (ModuleCat.restrictScalars g).obj M₂) :
    M₀ ⟶ (ModuleCat.restrictScalars (g.comp f)).obj M₂ :=
  α ≫ (ModuleCat.restrictScalars f).map β ≫
    (ModuleCat.restrictScalarsComp' f g (g.comp f) rfl).inv.app M₂

/-- On underlying elements, composition under scalar restriction is ordinary composition. -/
@[simp]
theorem homComp_apply (f : R →+* S) (g : S →+* T)
    {M₀ : ModuleCat.{x} R} {M₁ : ModuleCat.{x} S} {M₂ : ModuleCat.{x} T}
    (α : M₀ ⟶ (ModuleCat.restrictScalars f).obj M₁)
    (β : M₁ ⟶ (ModuleCat.restrictScalars g).obj M₂) (m : M₀) :
    (homComp f g α β).hom m = β.hom (α.hom m) := by
  simp [homComp]

end Composition

end Commutative

variable {R : Type u} {S : Type v} [CommRing R] [Ring S] [Algebra R S]

/-- The scalar actions supplied by an `IsScalarTower` agree with restriction
of scalars along the algebra map. -/
@[stacks 07VC "restriction-of-scalars identity comparison"]
theorem identityIso_smul
    (M : Type w) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (r : R) (m : M) :
    algebraMap R S r • m = r • m :=
  IsScalarTower.algebraMap_smul S r m

/-- A module with compatible `R`- and `S`-scalar structures is canonically
the same `R`-module as its restriction of scalars along `R → S`. -/
@[stacks 07VC "restriction-of-scalars identity comparison"]
noncomputable def identityIso
    (M : Type w) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] :
    (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S M) ≅ ModuleCat.of R M :=
  ({ __ := AddEquiv.refl M
     map_smul' := identityIso_smul M } :
    ((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S M)) ≃ₗ[R] M).toModuleIso

/-- The forward map of `identityIso` is the identity on elements. -/
@[simp, stacks 07VC]
theorem identityIso_hom_apply
    (M : Type w) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (m : M) :
    (identityIso (R := R) (S := S) M).hom m = m :=
  rfl

/-- The inverse map of `identityIso` is the identity on elements. -/
@[simp, stacks 07VC]
theorem identityIso_inv_apply
    (M : Type w) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (m : M) :
    (identityIso (R := R) (S := S) M).inv m = m :=
  rfl

end ModuleCat.RestrictScalars
