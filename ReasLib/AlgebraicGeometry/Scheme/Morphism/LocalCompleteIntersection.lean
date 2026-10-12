/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyOfType
public import ReasLib.RingTheory.CompleteIntersection.Local.Localization

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyOfType

/-- Scheme morphisms locally of complete-intersection type are canonically associated with
local complete-intersection ring homomorphisms. -/
instance instHasRingHomPropertyIsLocalCompleteIntersection :
    HasRingHomProperty
      (@AlgebraicGeometry.LocallyOfType.{u} RingHom.IsLocalCompleteIntersection)
      RingHom.IsLocalCompleteIntersection := sorry

/-- For a morphism of commutative rings, the induced morphism of affine spectra is locally of
complete-intersection type exactly when the ring morphism is a local complete intersection. -/
theorem isLocalCompleteIntersection_specMap_iff {A B : CommRingCat.{u}} (f : A ⟶ B) :
    AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection
        (AlgebraicGeometry.Spec.map f) ↔
      f.hom.IsLocalCompleteIntersection := sorry

end AlgebraicGeometry.LocallyOfType
