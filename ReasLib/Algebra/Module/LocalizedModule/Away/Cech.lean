/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Map
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The Principal-Open Cech Complex of a Module

This leaf owns the explicit first two maps of the Cech complex associated to
a family of principal opens.  Mathlib supplies the local-to-global exactness
criterion; the family and overlap maps here are the reusable concrete
interface needed by affine descent arguments.
-/

@[expose] public section

universe u v w z

namespace LocalizedModule.Away.Cech

variable {R : Type u} [CommSemiring R]
variable {ι : Type w}

/-- The canonical map from a module to the family of its principal-open localizations. -/
@[stacks 00EK "principal-open Cech family map"]
noncomputable def familyMap (M : Type v) [AddCommMonoid M] [Module R M] (f : ι → R) :
    M →ₗ[R] ∀ i : ι, LocalizedModule.Away (f i) M :=
  LinearMap.pi fun i ↦ LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M

/-- The `i`-th component of the principal-open Cech family map is the
canonical localization map away from `f i`. -/
@[simp, stacks 00EK "principal-open Cech family map application"]
theorem familyMap_apply
    (M : Type v) [AddCommMonoid M] [Module R M] (f : ι → R)
    (m : M) (i : ι) :
    familyMap M f m i =
      LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M m := sorry

/-- Restriction from the principal open `D(a)` to the intersection
`D(a * b)`. -/
@[stacks 00EK "principal-open overlap left restriction"]
noncomputable def restrictionLeft
    (M : Type v) [AddCommMonoid M] [Module R M] (a b : R) :
    LocalizedModule.Away a M →ₗ[R] LocalizedModule.Away (a * b) M :=
  LocalizedModule.Away.mapOfDvd a (a * b) (dvd_mul_right a b)

/-- Restriction from the principal open `D(b)` to the intersection
`D(a * b)`. -/
@[stacks 00EK "principal-open overlap right restriction"]
noncomputable def restrictionRight
    (M : Type v) [AddCommMonoid M] [Module R M] (a b : R) :
    LocalizedModule.Away b M →ₗ[R] LocalizedModule.Away (a * b) M :=
  LocalizedModule.Away.mapOfDvd b (a * b) (dvd_mul_left b a)

/-- The left overlap restriction sends a canonical localized element to its
canonical image on the intersection. -/
@[simp, stacks 00EK "principal-open overlap left restriction application"]
theorem restrictionLeft_apply_mk
    (M : Type v) [AddCommMonoid M] [Module R M] (a b : R) (m : M) :
    restrictionLeft M a b
        (LocalizedModule.mkLinearMap (Submonoid.powers a) M m) =
      LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) M m := sorry

/-- The right overlap restriction sends a canonical localized element to its
canonical image on the intersection. -/
@[simp, stacks 00EK "principal-open overlap right restriction application"]
theorem restrictionRight_apply_mk
    (M : Type v) [AddCommMonoid M] [Module R M] (a b : R) (m : M) :
    restrictionRight M a b
        (LocalizedModule.mkLinearMap (Submonoid.powers b) M m) =
      LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) M m := sorry

/-- The first Cech differential for a family of principal-open localizations. Its `(i, j)`
component is the difference of the two restrictions to `D(f i * f j)`. -/
@[stacks 00EK "principal-open Cech compatibility map"]
noncomputable def compatibilityMap
    (M : Type v) [AddCommGroup M] [Module R M] (f : ι → R) :
    (∀ i : ι, LocalizedModule.Away (f i) M) →ₗ[R]
      ∀ i : ι, ∀ j : ι, LocalizedModule.Away (f i * f j) M :=
  LinearMap.pi fun i ↦ LinearMap.pi fun j ↦
    (restrictionLeft M (f i) (f j)).comp (LinearMap.proj i) -
      (restrictionRight M (f i) (f j)).comp (LinearMap.proj j)

/-- The `(i, j)` component of the Cech differential is the left restriction
of the `i`-th entry minus the right restriction of the `j`-th entry. -/
@[simp, stacks 00EK "principal-open Cech compatibility component"]
theorem compatibilityMap_apply
    (M : Type v) [AddCommGroup M] [Module R M] (f : ι → R)
    (x : ∀ i : ι, LocalizedModule.Away (f i) M) (i j : ι) :
    compatibilityMap M f x i j =
      restrictionLeft M (f i) (f j) (x i) -
        restrictionRight M (f i) (f j) (x j) := sorry

/-- A linear map of modules induces the coordinatewise map on their families of principal-open
localizations. -/
@[stacks 00EK "principal-open Cech family map functoriality"]
noncomputable def mapFamily
    {M : Type v} {N : Type z} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (f : ι → R) (g : M →ₗ[R] N) :
    (∀ i : ι, LocalizedModule.Away (f i) M) →ₗ[R]
      ∀ i : ι, LocalizedModule.Away (f i) N :=
  LinearMap.piMap fun i ↦ LocalizedModule.Away.map (f i) g

/-- The map on principal-open families is coordinatewise localization of the
original linear map. -/
@[simp, stacks 00EK "principal-open Cech family map functoriality application"]
theorem mapFamily_apply
    {M : Type v} {N : Type z} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (f : ι → R) (g : M →ₗ[R] N)
    (x : ∀ i : ι, LocalizedModule.Away (f i) M) (i : ι) :
    mapFamily f g x i = LocalizedModule.Away.map (f i) g (x i) := sorry

/-- A linear map of modules induces the coordinatewise map on the pairwise overlaps of a
principal-open family. -/
@[stacks 00EK "principal-open Cech overlap map functoriality"]
noncomputable def overlapMap
    {M : Type v} {N : Type z} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (f : ι → R) (g : M →ₗ[R] N) :
    (∀ i : ι, ∀ j : ι, LocalizedModule.Away (f i * f j) M) →ₗ[R]
      ∀ i : ι, ∀ j : ι, LocalizedModule.Away (f i * f j) N :=
  LinearMap.piMap fun i ↦ LinearMap.piMap fun j ↦
    LocalizedModule.Away.map (f i * f j) g

/-- The map on pairwise overlaps is coordinatewise localization of the
original linear map. -/
@[simp, stacks 00EK "principal-open Cech overlap map functoriality application"]
theorem overlapMap_apply
    {M : Type v} {N : Type z} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (f : ι → R) (g : M →ₗ[R] N)
    (x : ∀ i : ι, ∀ j : ι, LocalizedModule.Away (f i * f j) M)
    (i j : ι) :
    overlapMap f g x i j = LocalizedModule.Away.map (f i * f j) g (x i j) := sorry

/-- The principal-open family maps are natural in the module. -/
@[stacks 00EK "principal-open Cech augmentation naturality"]
theorem mapFamily_comp_familyMap
    {M : Type v} {N : Type z} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (f : ι → R) (g : M →ₗ[R] N) :
    (mapFamily f g).comp (familyMap M f) = (familyMap N f).comp g := sorry

/-- The first principal-open Cech differential is natural in the module. -/
@[stacks 00EK "principal-open Cech compatibility naturality"]
theorem compatibilityMap_naturality
    {M : Type v} {N : Type z} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : ι → R) (g : M →ₗ[R] N) :
    (compatibilityMap N f).comp (mapFamily f g) =
      (overlapMap f g).comp (compatibilityMap M f) := sorry

/-- Consecutive maps in the principal-open Cech complex have zero composite. -/
@[stacks 00EK "principal-open Cech complex"]
theorem compatibilityMap_comp_familyMap
    (M : Type v) [AddCommGroup M] [Module R M] (f : ι → R) :
    (compatibilityMap M f).comp (familyMap M f) = 0 := sorry

end LocalizedModule.Away.Cech
