module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.BaseChange
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Restriction
public import ReasLib.CategoryTheory.Functor.MorphismPreimage
import Mathlib.Tactic.CrossRefAttribute

/-!
# Morphisms induced between associated module sheaves

This file records when a morphism between associated module sheaves comes from a morphism of
coefficient modules.  It also provides the canonical conjugated morphism after base change and
the corresponding open-local predicates.
-/

@[expose] public section

open CategoryTheory Filter TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Associated.Morphism

variable {X Y : RingedSpace.{u}} {R : Type u} [CommRing R]

/-- A morphism between associated sheaves is induced if it has a preimage under the associated
module functor. -/
@[stacks 01BL "induced morphism"]
def IsInduced (alpha : R →+* X.globalSectionsRing) {M N : ModuleCat.{u} R}
    (f : Associated.obj alpha M ⟶ Associated.obj alpha N) : Prop :=
  (Associated.functor alpha).HasPreimage f

/-- The pullback of a morphism between associated sheaves, conjugated by the canonical
base-change isomorphisms. -/
@[stacks 01BL "base-changed associated morphism"]
noncomputable def baseChangeMap (g : Y ⟶ X) (alpha : R →+* X.globalSectionsRing)
    {M N : ModuleCat.{u} R} (f : Associated.obj alpha M ⟶ Associated.obj alpha N) :
    Associated.obj (X := Y) (RingHom.id Y.globalSectionsRing) (BaseChange.obj g alpha M) ⟶
      Associated.obj (X := Y) (RingHom.id Y.globalSectionsRing) (BaseChange.obj g alpha N) :=
  (Associated.obj.baseChangeIso g alpha M).inv ≫
    (RingedSpace.Hom.pullback g).map f ≫
      (Associated.obj.baseChangeIso g alpha N).hom

namespace baseChangeMap

/-- Base-changing a morphism produced by the associated functor gives the morphism produced from
the scalar extension of the original module map. -/
@[stacks 01BL "base change of an induced morphism"]
theorem map (g : Y ⟶ X) (alpha : R →+* X.globalSectionsRing)
    {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    baseChangeMap g alpha ((Associated.functor alpha).map f) =
      (Associated.functor (X := Y) (RingHom.id Y.globalSectionsRing)).map
        ((BaseChange.functor g alpha).map f) := sorry

end baseChangeMap

/-- A morphism is induced after base change along `g` if its canonical conjugate has a preimage
under the identity-associated functor on the source. -/
@[stacks 01BL "induced after base change"]
def IsInducedAfter (g : Y ⟶ X) (alpha : R →+* X.globalSectionsRing)
    {M N : ModuleCat.{u} R} (f : Associated.obj alpha M ⟶ Associated.obj alpha N) : Prop :=
  IsInduced (X := Y) (RingHom.id Y.globalSectionsRing) (baseChangeMap g alpha f)

/-- Restriction of a morphism between associated sheaves to `U`, expressed between the
identity-associated scalar extensions on the restricted ringed space. -/
@[stacks 01BL "restricted associated morphism"]
noncomputable abbrev restrictedMap (alpha : R →+* X.globalSectionsRing)
    {M N : ModuleCat.{u} R} (f : Associated.obj alpha M ⟶ Associated.obj alpha N)
    (U : Opens X) :
    Associated.obj (X := X.restrict U.isOpenEmbedding)
        (RingHom.id (RingedSpace.globalSectionsRing (X.restrict U.isOpenEmbedding)))
        (BaseChange.obj (X.ofRestrict U.isOpenEmbedding) alpha M) ⟶
      Associated.obj (X := X.restrict U.isOpenEmbedding)
        (RingHom.id (RingedSpace.globalSectionsRing (X.restrict U.isOpenEmbedding)))
        (BaseChange.obj (X.ofRestrict U.isOpenEmbedding) alpha N) :=
  baseChangeMap (X.ofRestrict U.isOpenEmbedding) alpha f

namespace restrictedMap

/-- Restricting a morphism produced by the associated functor gives the morphism produced from
the scalar extension of the original module map to the open subspace. -/
@[stacks 01BL "restriction of an induced morphism"]
theorem map (alpha : R →+* X.globalSectionsRing) {M N : ModuleCat.{u} R}
    (f : M ⟶ N) (U : Opens X) :
    restrictedMap alpha ((Associated.functor alpha).map f) U =
      (Associated.functor (X := X.restrict U.isOpenEmbedding)
        (RingHom.id (RingedSpace.globalSectionsRing (X.restrict U.isOpenEmbedding)))).map
          ((BaseChange.functor (X.ofRestrict U.isOpenEmbedding) alpha).map f) := sorry

end restrictedMap

/-- A morphism between associated sheaves is induced on `U` if its restriction has a preimage
under the identity-associated functor on `X|_U`. -/
@[stacks 01BL "induced on an open"]
def IsInducedOn (alpha : R →+* X.globalSectionsRing) {M N : ModuleCat.{u} R}
    (f : Associated.obj alpha M ⟶ Associated.obj alpha N) (U : Opens X) : Prop :=
  IsInduced (X := X.restrict U.isOpenEmbedding)
    (RingHom.id (RingedSpace.globalSectionsRing (X.restrict U.isOpenEmbedding)))
    (restrictedMap alpha f U)

/-- A morphism between associated sheaves is locally induced at `x` if it is induced on some
open neighborhood of `x`. -/
@[stacks 01BL "locally induced at a point"]
def IsLocallyInducedAt (alpha : R →+* X.globalSectionsRing) {M N : ModuleCat.{u} R}
    (f : Associated.obj alpha M ⟶ Associated.obj alpha N) (x : X) : Prop :=
  ∃ (U : Opens X) (_ : x ∈ U), IsInducedOn alpha f U

namespace IsInduced

/-- Every morphism of coefficient modules induces a morphism of associated sheaves. -/
@[stacks 01BL "associated functor map"]
theorem map (alpha : R →+* X.globalSectionsRing) {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    IsInduced alpha ((Associated.functor alpha).map f) := sorry

/-- Induced morphisms are closed under composition. -/
@[stacks 01BL "composition"]
theorem comp {alpha : R →+* X.globalSectionsRing} {L M N : ModuleCat.{u} R}
    {f : Associated.obj alpha L ⟶ Associated.obj alpha M}
    {g : Associated.obj alpha M ⟶ Associated.obj alpha N}
    (hf : IsInduced alpha f) (hg : IsInduced alpha g) :
    IsInduced alpha (f ≫ g) := sorry

/-- An induced morphism remains induced after arbitrary base change. -/
@[stacks 01BL "base change"]
theorem baseChange {alpha : R →+* X.globalSectionsRing} {M N : ModuleCat.{u} R}
    {f : Associated.obj alpha M ⟶ Associated.obj alpha N}
    (hf : IsInduced alpha f) (g : Y ⟶ X) :
    IsInducedAfter g alpha f := sorry

end IsInduced

namespace IsInducedOn

/-- Being induced on an open is preserved by restriction to a smaller open. -/
@[stacks 01BL "restriction"]
theorem mono {alpha : R →+* X.globalSectionsRing} {M N : ModuleCat.{u} R}
    {f : Associated.obj alpha M ⟶ Associated.obj alpha N} {W U : Opens X}
    (hf : IsInducedOn alpha f U) (hWU : W ≤ U) :
    IsInducedOn alpha f W := sorry

end IsInducedOn

namespace IsLocallyInducedAt

/-- Local inducedness can be tested on any basis of open neighborhoods of the point. -/
@[stacks 01BL "local inducedness on a neighborhood basis"]
theorem iff_of_hasBasis {alpha : R →+* X.globalSectionsRing} {M N : ModuleCat.{u} R}
    {f : Associated.obj alpha M ⟶ Associated.obj alpha N} {x : X}
    {ι : Type*} {p : ι → Prop} {U : ι → Opens X}
    (hU : (nhds x).HasBasis p (fun i ↦ (U i : Set X))) :
    IsLocallyInducedAt alpha f x ↔ ∃ i, p i ∧ IsInducedOn alpha f (U i) := sorry

end IsLocallyInducedAt

end AlgebraicGeometry.RingedSpace.Module.Associated.Morphism
