/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Localization.Away.Basic
public import ReasLib.Algebra.Module.LocalizedModule.Away.Map
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Gluing Modules on a Principal-Open Cover

This leaf owns the data of a module on a family of principal opens together
with pairwise overlap identifications.  The local pieces remain bundled
`ModuleCat` objects over their own localization rings.  Opening Mathlib's
scoped `ModuleCat.Algebra` instances supplies the canonical base-ring views
without globally registering ambiguous scalar-restriction instances.
-/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u v w

namespace LocalizedModule.Away

variable {R : Type u} [CommRing R]
variable {ι : Type w}

namespace Gluing

/-- Tag `00EK`: pairwise overlap isomorphisms for local modules on a
principal-open family. -/
@[stacks 00EK "principal-open module overlap isomorphisms"]
abbrev OverlapIso (f : ι → R)
    (localModule : ∀ i, ModuleCat.{v} (Localization.Away (f i))) :=
  ∀ i j,
    ModuleCat.of (Localization.Away (f i * f j))
        (LocalizedModule.Away (f i * f j) (localModule i)) ≅
      ModuleCat.of (Localization.Away (f i * f j))
        (LocalizedModule.Away (f i * f j) (localModule j))

end Gluing

/-- Tag `00EK`: pairwise principal-open module gluing data, before imposing
the triple-overlap cocycle. -/
@[stacks 00EK "principal-open module pregluing datum"]
structure PreGluing (f : ι → R) where
  /-- The module carried by the principal open `D(f i)`. -/
  localModule : ∀ i, ModuleCat.{v} (Localization.Away (f i))
  /-- The identification of the two local pieces on `D(f i * f j)`. -/
  overlapIso : Gluing.OverlapIso f localModule

namespace PreGluing

variable {f : ι → R} (data : PreGluing f)

/-- Tag `00EK`: every local piece of a principal-open pregluing datum is
already localized away from its defining denominator. -/
@[stacks 00EK "principal-open pregluing local piece localization"]
instance localModule_isLocalized (i : ι) :
    IsLocalizedModule (Submonoid.powers (f i))
      (LinearMap.id : data.localModule i →ₗ[R] data.localModule i) :=
  isLocalizedModule_id (Submonoid.powers (f i)) (data.localModule i)
    (Localization.Away (f i))

/-- Tag `00EK`: restrict a pairwise overlap identification to a principal
open `D(d)` contained in the overlap.  The unit criterion is the intrinsic
algebraic form of this containment. -/
@[stacks 00EK "principal-open pregluing overlap restriction"]
noncomputable def overlapMap (i j : ι) (d : R)
    (h : IsUnit (algebraMap R (Localization.Away d) (f i * f j))) :
    LocalizedModule.Away d (data.localModule i) →ₗ[Localization.Away d]
      LocalizedModule.Away d (data.localModule j) :=
  (LocalizedModule.lift (Submonoid.powers d)
    ((LocalizedModule.Away.mapOfIsUnit (f i * f j) d h).comp
      (((data.overlapIso i j).toLinearEquiv.restrictScalars R).toLinearMap.comp
        (LocalizedModule.mkLinearMap (Submonoid.powers (f i * f j))
          (data.localModule i))))
    (fun s ↦ IsLocalizedModule.map_units
      (LocalizedModule.mkLinearMap (Submonoid.powers d) (data.localModule j)) s)).extendScalarsOfIsLocalization
    (Submonoid.powers d) (Localization.Away d)

/-- Restricting an overlap identification sends a canonical local section to
the corresponding restricted and transported canonical section. -/
@[simp, stacks 00EK "principal-open pregluing overlap restriction application"]
theorem overlapMap_apply_mk (i j : ι) (d : R)
    (h : IsUnit (algebraMap R (Localization.Away d) (f i * f j)))
    (x : data.localModule i) :
    data.overlapMap i j d h
        (LocalizedModule.mkLinearMap (Submonoid.powers d) (data.localModule i) x) =
      LocalizedModule.Away.mapOfIsUnit (f i * f j) d h
        ((data.overlapIso i j).toLinearEquiv
          (LocalizedModule.mkLinearMap (Submonoid.powers (f i * f j))
            (data.localModule i) x)) := sorry

/-- Tag `00EK`: transport across the first pair of a triple principal
overlap. -/
@[stacks 00EK "principal-open pregluing triple overlap map"]
noncomputable def tripleOverlapMap12 (i j k : ι) :
    LocalizedModule.Away (f i * f j * f k) (data.localModule i) →ₗ[Localization.Away (f i * f j * f k)]
      LocalizedModule.Away (f i * f j * f k) (data.localModule j) :=
  data.overlapMap i j (f i * f j * f k)
    (IsLocalization.Away.isUnit_of_dvd (f i * f j * f k)
      (dvd_mul_right (f i * f j) (f k)))

/-- Tag `00EK`: transport across the second pair of a triple principal
overlap. -/
@[stacks 00EK "principal-open pregluing triple overlap map"]
noncomputable def tripleOverlapMap23 (i j k : ι) :
    LocalizedModule.Away (f i * f j * f k) (data.localModule j) →ₗ[Localization.Away (f i * f j * f k)]
      LocalizedModule.Away (f i * f j * f k) (data.localModule k) :=
  data.overlapMap j k (f i * f j * f k)
    (IsLocalization.Away.isUnit_of_dvd (f i * f j * f k)
      (mul_dvd_mul_right (dvd_mul_left (f j) (f i)) (f k)))

/-- Tag `00EK`: direct transport across the outer pair of a triple principal
overlap. -/
@[stacks 00EK "principal-open pregluing triple overlap map"]
noncomputable def tripleOverlapMap13 (i j k : ι) :
    LocalizedModule.Away (f i * f j * f k) (data.localModule i) →ₗ[Localization.Away (f i * f j * f k)]
      LocalizedModule.Away (f i * f j * f k) (data.localModule k) :=
  data.overlapMap i k (f i * f j * f k)
    (IsLocalization.Away.isUnit_of_dvd (f i * f j * f k)
      (mul_dvd_mul_right (dvd_mul_right (f i) (f j)) (f k)))

/-- Tag `00EK`: the cocycle condition for pairwise module identifications on
the triple intersections of a principal-open family. -/
@[stacks 00EK "principal-open module gluing cocycle"]
def CocycleCondition : Prop :=
  ∀ i j k : ι,
    (data.tripleOverlapMap23 i j k).comp (data.tripleOverlapMap12 i j k) =
      data.tripleOverlapMap13 i j k

end PreGluing

/-- Tag `00EK`: a principal-open module gluing datum.  Its local pieces and
overlap isomorphisms are concrete data, and its triple-overlap law is
propositional. -/
@[stacks 00EK "principal-open module gluing datum"]
structure Gluing (f : ι → R) extends PreGluing f where
  /-- Compatibility of the pairwise identifications on triple overlaps. -/
  cocycle : PreGluing.CocycleCondition toPreGluing

namespace Gluing

variable {f : ι → R} (glue : Gluing f)

/-- Tag `00EK`: restrict a gluing overlap identification to a principal open
contained in that overlap. -/
@[stacks 00EK "principal-open gluing overlap restriction"]
noncomputable def overlapMap (i j : ι) (d : R)
    (h : IsUnit (algebraMap R (Localization.Away d) (f i * f j))) :
    LocalizedModule.Away d (glue.localModule i) →ₗ[Localization.Away d]
      LocalizedModule.Away d (glue.localModule j) :=
  glue.toPreGluing.overlapMap i j d h

/-- Restricting an overlap identification in a gluing datum sends a canonical
local section to the corresponding restricted and transported section. -/
@[simp, stacks 00EK "principal-open gluing overlap restriction application"]
theorem overlapMap_apply_mk (i j : ι) (d : R)
    (h : IsUnit (algebraMap R (Localization.Away d) (f i * f j)))
    (x : glue.localModule i) :
    glue.overlapMap i j d h
        (LocalizedModule.mkLinearMap (Submonoid.powers d) (glue.localModule i) x) =
      LocalizedModule.Away.mapOfIsUnit (f i * f j) d h
        ((glue.overlapIso i j).toLinearEquiv
          (LocalizedModule.mkLinearMap (Submonoid.powers (f i * f j))
            (glue.localModule i) x)) := sorry

/-- Tag `00EK`: transport across the first pair of a triple overlap in a
gluing datum. -/
@[stacks 00EK "principal-open gluing triple overlap map"]
noncomputable def tripleOverlapMap12 (i j k : ι) :
    LocalizedModule.Away (f i * f j * f k) (glue.localModule i) →ₗ[Localization.Away (f i * f j * f k)]
      LocalizedModule.Away (f i * f j * f k) (glue.localModule j) :=
  glue.toPreGluing.tripleOverlapMap12 i j k

/-- Tag `00EK`: transport across the second pair of a triple overlap in a
gluing datum. -/
@[stacks 00EK "principal-open gluing triple overlap map"]
noncomputable def tripleOverlapMap23 (i j k : ι) :
    LocalizedModule.Away (f i * f j * f k) (glue.localModule j) →ₗ[Localization.Away (f i * f j * f k)]
      LocalizedModule.Away (f i * f j * f k) (glue.localModule k) :=
  glue.toPreGluing.tripleOverlapMap23 i j k

/-- Tag `00EK`: direct transport across the outer pair of a triple overlap
in a gluing datum. -/
@[stacks 00EK "principal-open gluing triple overlap map"]
noncomputable def tripleOverlapMap13 (i j k : ι) :
    LocalizedModule.Away (f i * f j * f k) (glue.localModule i) →ₗ[Localization.Away (f i * f j * f k)]
      LocalizedModule.Away (f i * f j * f k) (glue.localModule k) :=
  glue.toPreGluing.tripleOverlapMap13 i j k

/-- The cocycle law evaluated at a section of a triple principal overlap. -/
@[stacks 00EK "principal-open gluing cocycle application"]
theorem cocycle_apply (i j k : ι)
    (x : LocalizedModule.Away (f i * f j * f k) (glue.localModule i)) :
    glue.tripleOverlapMap23 i j k (glue.tripleOverlapMap12 i j k x) =
      glue.tripleOverlapMap13 i j k x := sorry

/-- Tag `00EK`: the first restriction map from local-section families to
pairwise-overlap families. -/
@[stacks 00EK "principal-open gluing first restriction map"]
noncomputable def leftRestriction :
    (∀ i : ι, glue.localModule i) →ₗ[R]
      ∀ i : ι, ∀ j : ι,
        LocalizedModule.Away (f i * f j) (glue.localModule i) :=
  LinearMap.pi fun i ↦ LinearMap.pi fun j ↦
    (LocalizedModule.mkLinearMap (Submonoid.powers (f i * f j))
      (glue.localModule i)).comp (LinearMap.proj i)

/-- The `(i, j)` component of the first restriction map is the restriction
of the `i`-th local section to the common overlap. -/
@[simp, stacks 00EK "principal-open gluing first restriction component"]
theorem leftRestriction_apply
    (x : ∀ i : ι, glue.localModule i) (i j : ι) :
    glue.leftRestriction x i j =
      LocalizedModule.mkLinearMap (Submonoid.powers (f i * f j))
        (glue.localModule i) (x i) := sorry

/-- Tag `00EK`: the second restriction map from local-section families to
pairwise-overlap families, transported through the overlap identification. -/
@[stacks 00EK "principal-open gluing second restriction map"]
noncomputable def rightRestriction :
    (∀ i : ι, glue.localModule i) →ₗ[R]
      ∀ i : ι, ∀ j : ι,
        LocalizedModule.Away (f i * f j) (glue.localModule i) :=
  LinearMap.pi fun i ↦ LinearMap.pi fun j ↦
    (((glue.overlapIso i j).toLinearEquiv.restrictScalars R).symm.toLinearMap).comp
      ((LocalizedModule.mkLinearMap (Submonoid.powers (f i * f j))
        (glue.localModule j)).comp (LinearMap.proj j))

/-- The `(i, j)` component of the second restriction map is the restriction
of the `j`-th local section, transported back to the `i`-th overlap module. -/
@[simp, stacks 00EK "principal-open gluing second restriction component"]
theorem rightRestriction_apply
    (x : ∀ i : ι, glue.localModule i) (i j : ι) :
    glue.rightRestriction x i j =
      ((glue.overlapIso i j).toLinearEquiv.restrictScalars R).symm
        (LocalizedModule.mkLinearMap (Submonoid.powers (f i * f j))
          (glue.localModule j) (x j)) := sorry

/-- Tag `00EK`: the difference of the two restriction maps for a
principal-open module gluing.  This is a linear-algebraic companion to the
equalizer definition of `gluedModule`. -/
@[stacks 00EK "principal-open module gluing compatibility map"]
noncomputable def compatibilityMap :
    (∀ i : ι, glue.localModule i) →ₗ[R]
      ∀ i : ι, ∀ j : ι,
        LocalizedModule.Away (f i * f j) (glue.localModule i) :=
  glue.leftRestriction - glue.rightRestriction

/-- The `(i, j)` component of the gluing compatibility map is the difference
of the two restrictions to `D(f i * f j)`. -/
@[simp, stacks 00EK "principal-open module gluing compatibility component"]
theorem compatibilityMap_apply
    (x : ∀ i : ι, glue.localModule i) (i j : ι) :
    glue.compatibilityMap x i j =
      LocalizedModule.mkLinearMap (Submonoid.powers (f i * f j))
          (glue.localModule i) (x i) -
        ((glue.overlapIso i j).toLinearEquiv.restrictScalars R).symm
          (LocalizedModule.mkLinearMap (Submonoid.powers (f i * f j))
            (glue.localModule j) (x j)) := sorry

/-- Tag `00EK`: the module of compatible families of local sections, defined
as the equalizer of its two restrictions to pairwise overlaps. -/
@[stacks 00EK "principal-open glued module"]
noncomputable def gluedModule : Submodule R (∀ i : ι, glue.localModule i) :=
  LinearMap.eqLocus glue.leftRestriction glue.rightRestriction

/-- The equalizer definition of the glued module agrees with the kernel of
the difference compatibility map. -/
@[stacks 00EK "principal-open glued module kernel description"]
theorem gluedModule_eq_ker_compatibilityMap :
    glue.gluedModule = LinearMap.ker glue.compatibilityMap := sorry

/-- A family belongs to the glued module exactly when its two restrictions
agree on every pairwise overlap. -/
@[stacks 00EK "principal-open glued module membership"]
theorem mem_gluedModule_iff (x : ∀ i : ι, glue.localModule i) :
    x ∈ glue.gluedModule ↔
      ∀ i j : ι,
        LocalizedModule.mkLinearMap (Submonoid.powers (f i * f j))
            (glue.localModule i) (x i) =
          ((glue.overlapIso i j).toLinearEquiv.restrictScalars R).symm
            (LocalizedModule.mkLinearMap (Submonoid.powers (f i * f j))
            (glue.localModule j) (x j)) := sorry

/-- Tag `00EK`: the projection from compatible local sections to the local
section on the principal open `D(f i)`. -/
@[stacks 00EK "principal-open glued module projection"]
noncomputable def projection (i : ι) : glue.gluedModule →ₗ[R] glue.localModule i :=
  (LinearMap.proj i).comp glue.gluedModule.subtype

/-- The `i`-th projection of a compatible family is its `i`-th coordinate. -/
@[simp, stacks 00EK "principal-open glued module projection application"]
theorem projection_apply (i : ι) (m : glue.gluedModule) :
    glue.projection i m = m.1 i := sorry

/-- Tag `00EQ` (2): a compatible family has equal images on each pairwise
principal overlap after applying the given overlap identification. -/
@[stacks 00EQ "principal-open gluing overlap formula"]
theorem overlapIso_projection_mk (i j : ι) (m : glue.gluedModule) :
    (glue.overlapIso i j).toLinearEquiv
        (LocalizedModule.mkLinearMap (Submonoid.powers (f i * f j))
          (glue.localModule i) (glue.projection i m)) =
      LocalizedModule.mkLinearMap (Submonoid.powers (f i * f j))
        (glue.localModule j) (glue.projection j m) := sorry

/-- Tag `00EK`: the localization of the `i`-th projection.  The target local
piece carries the canonical localization instance supplied by the pregluing
datum. -/
@[stacks 00EK "principal-open glued module localized projection"]
noncomputable def localizedProjection (i : ι) :
    LocalizedModule.Away (f i) glue.gluedModule →ₗ[Localization.Away (f i)]
      glue.localModule i :=
  (IsLocalizedModule.map (Submonoid.powers (f i))
      (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) glue.gluedModule)
      (LinearMap.id : glue.localModule i →ₗ[R] glue.localModule i)
      (glue.projection i)).extendScalarsOfIsLocalization
        (Submonoid.powers (f i)) (Localization.Away (f i))

/-- The localized projection sends the canonical image of a compatible family
to its `i`-th coordinate. -/
@[simp, stacks 00EK "principal-open glued module localized projection application"]
theorem localizedProjection_apply_mk (i : ι) (x : glue.gluedModule) :
    glue.localizedProjection i
        (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) glue.gluedModule x) =
      glue.projection i x := sorry

end Gluing

end LocalizedModule.Away
