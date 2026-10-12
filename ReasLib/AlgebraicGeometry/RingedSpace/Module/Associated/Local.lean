/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Compactness.LocallyCompact
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.BaseChange
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Quasicoherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Restriction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Locally associated module sheaves

This file packages the property that a module sheaf becomes associated to a module over global
sections after restriction to a neighborhood.  It provides pointwise and space-wide forms of the
property, together with the quasi-coherent criterion on spaces with compact neighborhood bases.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry Topology

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Associated

variable {X : RingedSpace.{u}}

/-- A module sheaf is associated on `U` if its restriction to `X|_U` is isomorphic to the sheaf
associated to a module over `Γ(X|_U, O_{X|_U})`. -/
@[stacks 01BK "associated on an open"]
def IsAssociatedOn (F : X.Modules) (U : Opens X) : Prop :=
  (Associated.functor
      (X := X.restrict U.isOpenEmbedding)
      (RingHom.id (RingedSpace.globalSectionsRing (X.restrict U.isOpenEmbedding)))).essImage
    ((X.moduleRestrictionToOpen U).obj F)

/-- A module sheaf is associated at `x` if it is associated on some open neighborhood of `x`. -/
@[stacks 01BK "associated at a point"]
def IsAssociatedAt (F : X.Modules) (x : X) : Prop :=
  ∃ (U : Opens X) (_ : x ∈ U), IsAssociatedOn F U

/-- A module sheaf is locally associated if it is associated at every point. -/
@[stacks 01BK "locally associated"]
def IsLocallyAssociated (F : X.Modules) : Prop :=
  ∀ x, IsAssociatedAt F x

namespace IsAssociatedOn

/-- Being associated on a fixed open is closed under module-sheaf isomorphisms. -/
instance isClosedUnderIsomorphisms (U : Opens X) :
    ObjectProperty.IsClosedUnderIsomorphisms
      (fun F : X.Modules => IsAssociatedOn F U) := sorry

/-- Transport association on an open across a module-sheaf isomorphism. -/
theorem of_iso {F G : X.Modules} (e : F ≅ G) (U : Opens X)
    (hF : IsAssociatedOn F U) : IsAssociatedOn G U := sorry

/-- Association on an open is equivalent on isomorphic module sheaves. -/
theorem iff_of_iso {F G : X.Modules} (e : F ≅ G) (U : Opens X) :
    IsAssociatedOn F U ↔ IsAssociatedOn G U := sorry

/-- A module sheaf is associated on `U` exactly when its restriction is isomorphic to the
associated sheaf of some module over the global-sections ring of `X|_U`. -/
@[stacks 01BK "witness form"]
theorem iffExistsIso (F : X.Modules) (U : Opens X) :
    IsAssociatedOn F U ↔
      ∃ M : ModuleCat
          (RingedSpace.globalSectionsRing (X.restrict U.isOpenEmbedding)),
        Nonempty
          ((X.moduleRestrictionToOpen U).obj F ≅
            obj (X := X.restrict U.isOpenEmbedding)
              (RingHom.id
                (RingedSpace.globalSectionsRing (X.restrict U.isOpenEmbedding))) M) := sorry

/-- Being associated on an open is preserved by restriction to a smaller open. -/
@[stacks 01BK "restriction"]
theorem mono {F : X.Modules} {W U : Opens X} (hFU : IsAssociatedOn F U) (hWU : W ≤ U) :
    IsAssociatedOn F W := sorry

end IsAssociatedOn

namespace IsAssociatedAt

/-- Being associated at a point is closed under module-sheaf isomorphisms. -/
instance isClosedUnderIsomorphisms (x : X) :
    ObjectProperty.IsClosedUnderIsomorphisms
      (fun F : X.Modules => IsAssociatedAt F x) := sorry

/-- Transport pointwise association across a module-sheaf isomorphism. -/
theorem of_iso {F G : X.Modules} (e : F ≅ G) (x : X)
    (hF : IsAssociatedAt F x) : IsAssociatedAt G x := sorry

/-- Pointwise association is equivalent on isomorphic module sheaves. -/
theorem iff_of_iso {F G : X.Modules} (e : F ≅ G) (x : X) :
    IsAssociatedAt F x ↔ IsAssociatedAt G x := sorry

/-- Lemma 17.10.8 (01BK): a quasi-coherent module sheaf is associated at every point admitting
a basis of compact neighborhoods. -/
@[stacks 01BK]
theorem ofIsQuasicoherent (F : X.Modules) [F.IsQuasicoherent] {x : X}
    (hx : (𝓝 x).HasBasis (fun K : Set X ↦ K ∈ 𝓝 x ∧ IsCompact K) id) :
    IsAssociatedAt F x := sorry

end IsAssociatedAt

namespace IsLocallyAssociated

/-- Local association is closed under module-sheaf isomorphisms. -/
instance isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms
      (IsLocallyAssociated : ObjectProperty X.Modules) := sorry

/-- Transport local association across a module-sheaf isomorphism. -/
theorem of_iso {F G : X.Modules} (e : F ≅ G)
    (hF : IsLocallyAssociated F) : IsLocallyAssociated G := sorry

/-- Local association is equivalent on isomorphic module sheaves. -/
theorem iff_of_iso {F G : X.Modules} (e : F ≅ G) :
    IsLocallyAssociated F ↔ IsLocallyAssociated G := sorry

/-- On a locally compact ringed space, every quasi-coherent module sheaf is locally associated. -/
@[stacks 01BK "locally compact space"]
theorem ofIsQuasicoherent (F : X.Modules) [F.IsQuasicoherent] [LocallyCompactSpace X] :
    IsLocallyAssociated F := sorry

end IsLocallyAssociated

end AlgebraicGeometry.RingedSpace.Module.Associated
