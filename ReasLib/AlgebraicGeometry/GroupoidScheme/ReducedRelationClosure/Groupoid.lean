module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Pair
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Morphism.ReducedImageClosure.Groupoid

/-!
# Reduced relation-closure groupoids

This module constructs a groupoid scheme on the reduced closure of the canonical relation
of a groupoid scheme whose object scheme is the spectrum of a perfect field.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- If the object scheme of a groupoid scheme is the spectrum of a perfect field, the
reduced closed subscheme supported on the closure of the image of `(t, s)` is the arrow
scheme of a groupoid over the same base. -/
noncomputable def reducedRelationClosure
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    (G : GroupoidScheme S) (eU : Spec (CommRingCat.of k) ≅ G.U.left) : GroupoidScheme S :=
  Hom.reducedImageClosure eU (toPair_object_eq G) (toPair G)
    (toPair_isIdentityOnObjects G)

/-- The object scheme of the reduced relation closure is the original object scheme. -/
theorem reducedRelationClosure_U
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    (G : GroupoidScheme S) (eU : Spec (CommRingCat.of k) ≅ G.U.left) :
    (reducedRelationClosure G eU).U = G.U := by
  simpa [reducedRelationClosure, pair_U] using
    Hom.reducedImageClosure_U eU (toPair_object_eq G) (toPair G)
      (toPair_isIdentityOnObjects G)

/-- The arrow scheme is the reduced closed subscheme supported on the closure of the image
of the canonical arrow map to the pair groupoid, equivalently of `(t, s)`. -/
theorem reducedRelationClosure_R
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    (G : GroupoidScheme S) (eU : Spec (CommRingCat.of k) ≅ G.U.left) :
    (reducedRelationClosure G eU).R =
      Scheme.Hom.reducedImageClosureOver (toPair G).arrow := by
  change
    (Hom.reducedImageClosure eU (toPair_object_eq G) (toPair G)
      (toPair_isIdentityOnObjects G)).R =
      Scheme.Hom.reducedImageClosureOver (toPair G).arrow
  exact
    Hom.reducedImageClosure_R eU (toPair_object_eq G) (toPair G)
      (toPair_isIdentityOnObjects G)

/-- The source map is the second projection restricted to the reduced relation closure. -/
theorem reducedRelationClosure_s
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    (G : GroupoidScheme S) (eU : Spec (CommRingCat.of k) ≅ G.U.left) :
    (reducedRelationClosure G eU).s =
      Scheme.Hom.reducedImageClosureιOver (toPair G).arrow ≫ (pair G.U).s := by
  simpa [reducedRelationClosure] using
    Hom.reducedImageClosure_s eU (toPair_object_eq G) (toPair G)
      (toPair_isIdentityOnObjects G)

/-- The target map is the first projection restricted to the reduced relation closure. -/
theorem reducedRelationClosure_t
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    (G : GroupoidScheme S) (eU : Spec (CommRingCat.of k) ≅ G.U.left) :
    (reducedRelationClosure G eU).t =
      Scheme.Hom.reducedImageClosureιOver (toPair G).arrow ≫ (pair G.U).t := by
  simpa [reducedRelationClosure] using
    Hom.reducedImageClosure_t eU (toPair_object_eq G) (toPair G)
      (toPair_isIdentityOnObjects G)

/-- Composition is the canonical restriction of the outer-pair map `pr02`. -/
theorem reducedRelationClosure_c
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    (G : GroupoidScheme S) (eU : Spec (CommRingCat.of k) ≅ G.U.left) :
    (reducedRelationClosure G eU).c =
      Hom.reducedImageClosureCompositionLift eU (toPair_object_eq G) (toPair G)
        (toPair_isIdentityOnObjects G) := by
  simpa [reducedRelationClosure] using
    Hom.reducedImageClosure_c eU (toPair_object_eq G) (toPair G)
      (toPair_isIdentityOnObjects G)

/-- The identity map is the canonical lift of the diagonal into the reduced relation closure. -/
theorem reducedRelationClosure_e
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    (G : GroupoidScheme S) (eU : Spec (CommRingCat.of k) ≅ G.U.left) :
    (reducedRelationClosure G eU).e =
      Hom.reducedImageClosureIdentity eU (toPair_object_eq G) (toPair G)
        (toPair_isIdentityOnObjects G) := by
  simpa [reducedRelationClosure] using
    Hom.reducedImageClosure_e eU (toPair_object_eq G) (toPair G)
      (toPair_isIdentityOnObjects G)

/-- Inversion is the canonical restriction of factor swap on the pair groupoid. -/
theorem reducedRelationClosure_i
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    (G : GroupoidScheme S) (eU : Spec (CommRingCat.of k) ≅ G.U.left) :
    (reducedRelationClosure G eU).i =
      Hom.reducedImageClosureInverse (toPair_object_eq G) (toPair G)
        (toPair_isIdentityOnObjects G) := by
  simpa [reducedRelationClosure] using
    Hom.reducedImageClosure_i eU (toPair_object_eq G) (toPair G)
      (toPair_isIdentityOnObjects G)

end AlgebraicGeometry.GroupoidScheme
