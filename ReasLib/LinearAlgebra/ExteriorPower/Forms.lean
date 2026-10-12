/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic

@[expose] public section

/-!
# Forms built from exterior powers

This file packages the degree-indexed family consisting of a base ring, a module, and its higher
exterior powers.  It is independent of a choice of differential or a scalar tower.  Since its
terms include both the base ring and exterior powers, the family keeps them in one universe rather
than exposing `ULift` in every degree.
-/

namespace exteriorPower

universe u v

/-- The degree-`p` term formed from a commutative ring `B` and a `B`-module `M`: degree `0` is
`B`, degree `1` is `M`, and degree `p + 2` is the corresponding exterior power of `M`. -/
@[stacks 07HY]
def form
    (B : Type u) [CommRing B]
    (M : Type u) [AddCommGroup M] [Module B M] : ℕ → Type u
  | 0 => B
  | 1 => M
  | p + 2 => ⋀[B]^(p + 2) M

namespace form

section

variable {B : Type u} [CommRing B]
variable {M : Type u} [AddCommGroup M] [Module B M]

/-- Every term of `exteriorPower.form B M` carries its canonical additive commutative group
structure. -/
@[reducible, instance]
def addCommGroup (p : ℕ) : AddCommGroup (form B M p) :=
  match p with
  | 0 => (inferInstance : AddCommGroup B)
  | 1 => (inferInstance : AddCommGroup M)
  | q + 2 => (inferInstance : AddCommGroup (⋀[B]^(q + 2) M))

/-- Every term of `exteriorPower.form B M` carries its canonical `B`-module structure. -/
@[reducible, instance]
def module (p : ℕ) : Module B (form B M p) :=
  match p with
  | 0 => (inferInstance : Module B B)
  | 1 => (inferInstance : Module B M)
  | q + 2 => (inferInstance : Module B (⋀[B]^(q + 2) M))

end

section

variable {A : Type v} [CommRing A]
variable {B : Type u} [CommRing B] [Algebra A B]
variable {M : Type u} [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]

/-- The `A`-module structure on a term of `exteriorPower.form B M` induced by a scalar tower.

This is deliberately not an instance: in degree one it preserves the caller's chosen `A`-module
structure on `M`, which need not be definitionally equal to `Module.compHom`. -/
abbrev moduleOfScalarTower (p : ℕ) : Module A (form B M p) :=
  match p with
  | 0 => (inferInstance : Module A B)
  | 1 => (inferInstance : Module A M)
  | _ + 2 => Module.compHom _ (algebraMap A B)

/-- The module selected by `moduleOfScalarTower` is compatible with the original `B`-module
structure. -/
theorem isScalarTower_moduleOfScalarTower (p : ℕ) :
    -- Local instance justification (defeq pin): preserve the fixed degree-dependent action.
    letI : Module A (form B M p) := moduleOfScalarTower (A := A) (B := B) (M := M) p
    IsScalarTower A B (form B M p) := sorry

/-- The original `B`-action commutes with the scalar-tower `A`-action on every exterior-form
term. -/
theorem smulCommClass_moduleOfScalarTower (p : ℕ) :
    -- Local instance justification (defeq pin): preserve the fixed degree-dependent action.
    letI : Module A (form B M p) := moduleOfScalarTower (A := A) (B := B) (M := M) p
    SMulCommClass B A (form B M p) := sorry

end

end form

namespace form

variable {B : Type u} [CommRing B]
variable {M : Type u} [AddCommGroup M] [Module B M]
variable {N : Type u} [AddCommGroup N] [Module B N]

/-- The degreewise map on `exteriorPower.form` induced by a `B`-linear map. It is the identity
in degree `0`, the given map in degree `1`, and the induced exterior-power map in higher degrees.
-/
noncomputable def map (f : M →ₗ[B] N) :
    ∀ p : ℕ, form B M p →ₗ[B] form B N p
  | 0 => LinearMap.id
  | 1 => f
  | p + 2 => exteriorPower.map (p + 2) f

/-- The degree-zero component of `form.map` is the identity of the base ring. -/
@[simp]
theorem map_zero (f : M →ₗ[B] N) :
    map f 0 = (LinearMap.id : B →ₗ[B] B) := sorry

/-- The degree-one component of `form.map` is its defining linear map. -/
@[simp]
theorem map_one (f : M →ₗ[B] N) :
    map f 1 = f := sorry

/-- In higher degree, `form.map` is the map induced on exterior powers. -/
@[simp]
theorem map_succ_succ (f : M →ₗ[B] N) (p : ℕ) :
    map f (p + 2) = exteriorPower.map (p + 2) f := sorry

/-- In higher degree, `form.map` sends an exterior generator to the exterior generator of its
entrywise image. -/
@[simp]
theorem map_succ_succ_apply_ιMulti (f : M →ₗ[B] N) (p : ℕ)
    (m : Fin (p + 2) → M) :
    map f (p + 2) (ιMulti B (p + 2) m) = ιMulti B (p + 2) (f ∘ m) := sorry

/-- `form.map` for the identity map is degreewise the identity. -/
@[simp]
theorem map_id (p : ℕ) :
    map (LinearMap.id : M →ₗ[B] M) p = LinearMap.id := sorry

variable {P : Type u} [AddCommGroup P] [Module B P]

/-- `form.map` respects composition of linear maps. -/
@[simp]
theorem map_comp (g : N →ₗ[B] P) (f : M →ₗ[B] N) (p : ℕ) :
    map (g.comp f) p = (map g p).comp (map f p) := sorry

/-- A surjective linear map induces a surjection on every degree of `exteriorPower.form`. -/
theorem map_surjective (f : M →ₗ[B] N) (hf : Function.Surjective f) (p : ℕ) :
    Function.Surjective (map f p) := sorry

end form

namespace form

section

variable {A : Type v} {B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {M : Type u} [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
variable {N : Type u} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]

/-- A `B`-submodule of an exterior-form term, regarded as an `A`-submodule through the
scalar-tower action selected by `form.moduleOfScalarTower`.

This fixes the action on the raw carrier in the same way as `form.Hom`, so degree one retains the
given `A`-module structure on `M`. -/
def restrictScalars (A : Type v) [CommRing A] [Algebra A B]
    [Module A M] [IsScalarTower A B M]
    {p : ℕ} (U : Submodule B (form B M p)) :
    -- Local instance justification (defeq pin): preserve the caller's degree-one scalar action.
    letI : Module A (form B M p) := moduleOfScalarTower (A := A) (B := B) (M := M) p
    Submodule A (form B M p) :=
  -- Local instance justification (defeq pin): preserve the fixed degree-dependent action.
  letI : Module A (form B M p) := moduleOfScalarTower (A := A) (B := B) (M := M) p
  -- Local instance justification (defeq pin): preserve the canonical scalar-tower witness for the fixed action.
  letI : IsScalarTower A B (form B M p) :=
    isScalarTower_moduleOfScalarTower (A := A) (B := B) (M := M) p
  U.restrictScalars A

/-- Membership in `form.restrictScalars` is membership in the original `B`-submodule. -/
@[simp]
theorem restrictScalars_mem (A : Type v) [CommRing A] [Algebra A B]
    [Module A M] [IsScalarTower A B M]
    {p : ℕ} (U : Submodule B (form B M p)) (x : form B M p) :
    -- Local instance justification (defeq pin): preserve the fixed degree-dependent action.
    letI : Module A (form B M p) := moduleOfScalarTower (A := A) (B := B) (M := M) p
    x ∈ restrictScalars A U ↔ x ∈ U := sorry

/-- `A`-linear maps between exterior-form terms with their scalar-tower module structures fixed.

This owner prevents each consumer from independently selecting a module structure on the raw
carrier `form B M p`; degree one retains the supplied `A`-action on `M`. -/
abbrev Hom
    (A : Type v) [CommRing A]
    (B : Type u) [CommRing B] [Algebra A B]
    (M : Type u) [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    (N : Type u) [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (p q : ℕ) :=
  -- Local instance justification (defeq pin): preserve the fixed source degree action.
  letI : Module A (form B M p) := moduleOfScalarTower (A := A) (B := B) (M := M) p
  -- Local instance justification (defeq pin): preserve the fixed target degree action.
  letI : Module A (form B N q) := moduleOfScalarTower (A := A) (B := B) (M := N) q
  form B M p →ₗ[A] form B N q

/-- Two fixed-action exterior-form maps are equal when they agree on every input. -/
@[ext]
theorem Hom.ext {p q : ℕ} (f g : Hom A B M N p q)
    (h : ∀ x, f x = g x) : f = g := sorry

/-- The kernel of a fixed-action exterior-form map.

The degree-dependent scalar action is selected inside this owner, so consumers can compare
kernels without rebuilding local `Module A` instances on the raw exterior-power carriers. -/
def ker {p q : ℕ} (f : Hom A B M N p q) :
    -- Local instance justification (defeq pin): preserve the fixed source degree action.
    letI : Module A (form B M p) := moduleOfScalarTower (A := A) (B := B) (M := M) p
    Submodule A (form B M p) :=
  -- Local instance justification (defeq pin): preserve the fixed source degree action.
  letI : Module A (form B M p) := moduleOfScalarTower (A := A) (B := B) (M := M) p
  -- Local instance justification (defeq pin): preserve the fixed target degree action.
  letI : Module A (form B N q) := moduleOfScalarTower (A := A) (B := B) (M := N) q
  let f' : form B M p →ₗ[A] form B N q := f
  LinearMap.ker f'

/-- The range of a fixed-action exterior-form map.

The degree-dependent scalar action is selected inside this owner, so consumers can compare
ranges without rebuilding local `Module A` instances on the raw exterior-power carriers. -/
def range {p q : ℕ} (f : Hom A B M N p q) :
    -- Local instance justification (defeq pin): preserve the fixed target degree action.
    letI : Module A (form B N q) := moduleOfScalarTower (A := A) (B := B) (M := N) q
    Submodule A (form B N q) :=
  -- Local instance justification (defeq pin): preserve the fixed source degree action.
  letI : Module A (form B M p) := moduleOfScalarTower (A := A) (B := B) (M := M) p
  -- Local instance justification (defeq pin): preserve the fixed target degree action.
  letI : Module A (form B N q) := moduleOfScalarTower (A := A) (B := B) (M := N) q
  let f' : form B M p →ₗ[A] form B N q := f
  LinearMap.range f'

/-- The degreewise exterior-form map induced by a `B`-linear map, regarded as `A`-linear through
the given scalar towers. -/
@[stacks 07HY]
noncomputable def mapRestrictScalars (A : Type v) [CommRing A] [Algebra A B]
    [Module A M] [IsScalarTower A B M] [Module A N] [IsScalarTower A B N]
    (f : M →ₗ[B] N) (p : ℕ) : Hom A B M N p p :=
  -- Local instance justification (defeq pin): preserve the fixed source degree action.
  letI : Module A (form B M p) := moduleOfScalarTower (A := A) (B := B) (M := M) p
  -- Local instance justification (defeq pin): preserve the fixed target degree action.
  letI : Module A (form B N p) := moduleOfScalarTower (A := A) (B := B) (M := N) p
  -- Local instance justification (defeq pin): preserve the canonical scalar-tower witness for the fixed source action.
  letI : IsScalarTower A B (form B M p) :=
    isScalarTower_moduleOfScalarTower (A := A) (B := B) (M := M) p
  -- Local instance justification (defeq pin): preserve the canonical scalar-tower witness for the fixed target action.
  letI : IsScalarTower A B (form B N p) :=
    isScalarTower_moduleOfScalarTower (A := A) (B := B) (M := N) p
  (map f p).restrictScalars A

/-- In degree zero, `mapRestrictScalars` is the identity on the coefficient ring. -/
@[simp]
theorem mapRestrictScalars_zero_apply (A : Type v) [CommRing A] [Algebra A B]
    [Module A M] [IsScalarTower A B M] [Module A N] [IsScalarTower A B N]
    (f : M →ₗ[B] N) (b : B) :
    mapRestrictScalars A f 0 b = b := sorry

/-- In degree one, `mapRestrictScalars` is the original map with scalars restricted to `A`. -/
@[simp]
theorem mapRestrictScalars_one (A : Type v) [CommRing A] [Algebra A B]
    [Module A M] [IsScalarTower A B M] [Module A N] [IsScalarTower A B N]
    (f : M →ₗ[B] N) :
    mapRestrictScalars A f 1 = f.restrictScalars A := sorry

/-- On a higher-degree exterior generator, `mapRestrictScalars` acts entrywise. -/
@[simp]
theorem mapRestrictScalars_succ_succ_apply_ιMulti (A : Type v) [CommRing A] [Algebra A B]
    [Module A M] [IsScalarTower A B M] [Module A N] [IsScalarTower A B N]
    (f : M →ₗ[B] N) (p : ℕ) (m : Fin (p + 2) → M) :
    mapRestrictScalars A f (p + 2) (ιMulti B (p + 2) m) =
      ιMulti B (p + 2) (f ∘ m) := sorry

/-- Restricting scalars preserves identity maps on every exterior-form degree. -/
@[simp]
theorem mapRestrictScalars_id_apply (A : Type v) [CommRing A] [Algebra A B]
    [Module A M] [IsScalarTower A B M]
    (p : ℕ) (x : form B M p) :
    mapRestrictScalars A (LinearMap.id : M →ₗ[B] M) p x = x := sorry

variable {P : Type u} [AddCommGroup P] [Module B P] [Module A P] [IsScalarTower A B P]

/-- Restricting scalars preserves composition of maps between exterior-form terms. -/
@[simp]
theorem mapRestrictScalars_comp (A : Type v) [CommRing A] [Algebra A B]
    [Module A M] [IsScalarTower A B M] [Module A N] [IsScalarTower A B N]
    [Module A P] [IsScalarTower A B P]
    (g : N →ₗ[B] P) (f : M →ₗ[B] N) (p : ℕ) :
    mapRestrictScalars A (g.comp f) p =
      (mapRestrictScalars A g p).comp (mapRestrictScalars A f p) := sorry

/-- A surjective map induces a surjection on every degree of the associated exterior-form
family, also after restricting scalars along `A → B`. -/
theorem mapRestrictScalars_surjective (A : Type v) [CommRing A] [Algebra A B]
    [Module A M] [IsScalarTower A B M] [Module A N] [IsScalarTower A B N]
    (f : M →ₗ[B] N) (hf : Function.Surjective f) (p : ℕ) :
    Function.Surjective (mapRestrictScalars A f p) := sorry

/-- The kernel of a fixed-action exterior-form map is the scalar restriction of the kernel of
the underlying `B`-linear exterior-form map. -/
theorem mapRestrictScalars_ker (A : Type v) [CommRing A] [Algebra A B]
    [Module A M] [IsScalarTower A B M] [Module A N] [IsScalarTower A B N]
    (f : M →ₗ[B] N) (p : ℕ) :
    ker (mapRestrictScalars A f p) =
      restrictScalars A (LinearMap.ker (map f p)) := sorry

/-- The range of a fixed-action exterior-form map is the scalar restriction of the range of
the underlying `B`-linear exterior-form map. -/
theorem mapRestrictScalars_range (A : Type v) [CommRing A] [Algebra A B]
    [Module A M] [IsScalarTower A B M] [Module A N] [IsScalarTower A B N]
    (f : M →ₗ[B] N) (p : ℕ) :
    range (mapRestrictScalars A f p) =
      restrictScalars A (LinearMap.range (map f p)) := sorry

end

end form

end exteriorPower
