module

public import Mathlib.CategoryTheory.Elements
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.AlgebraicGeometry.FormalDeformation.Prorepresentable
public import ReasLib.CategoryTheory.Groupoid.InFunctors
public import ReasLib.CategoryTheory.Groupoid.InFunctors.Representability
public import ReasLib.CategoryTheory.Groupoid.InFunctors.Restriction

/-!
# Prorepresentable groupoids in functors

A groupoid in functors on `ArtinianLocalAlgCat Λ k` is prorepresentable when both
its object functor and its arrow functor are prorepresentable.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

universe u v w

namespace CategoryTheory.GroupoidInFunctors

section SourceTarget

variable {C : Type u} [Category.{v} C]

/-- The based functor over `C` induced by the source map of a groupoid in functors. -/
def sourceBasedFunctor (G : GroupoidInFunctors C) :
    BasedCategory.ofFunctor (CategoryOfElements.π G.R) ⥤ᵇ
      BasedCategory.ofFunctor (CategoryOfElements.π G.U) :=
  BasedFunctor.ofFunctor (CategoryOfElements.map G.s) (CategoryOfElements.map_π G.s)

/-- The underlying functor of `sourceBasedFunctor` is the category-of-elements map of `s`. -/
theorem sourceBasedFunctor_toFunctor (G : GroupoidInFunctors C) :
    (sourceBasedFunctor G).toFunctor = CategoryOfElements.map G.s :=
  rfl

/-- The based functor over `C` induced by the target map of a groupoid in functors. -/
def targetBasedFunctor (G : GroupoidInFunctors C) :
    BasedCategory.ofFunctor (CategoryOfElements.π G.R) ⥤ᵇ
      BasedCategory.ofFunctor (CategoryOfElements.π G.U) :=
  BasedFunctor.ofFunctor (CategoryOfElements.map G.t) (CategoryOfElements.map_π G.t)

/-- The underlying functor of `targetBasedFunctor` is the category-of-elements map of `t`. -/
theorem targetBasedFunctor_toFunctor (G : GroupoidInFunctors C) :
    (targetBasedFunctor G).toFunctor = CategoryOfElements.map G.t :=
  rfl

end SourceTarget

section Prorepresentable

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- Both the object and arrow functors have complete local prorepresentations. -/
class IsProrepresentableFunctors
    (U R : ArtinianLocalAlgCat Λ k ⥤ Type u) : Prop where
  /-- The object functor admits a prorepresentation. -/
  isProrepresentable_U : Functor.IsProrepresentable U
  /-- The arrow functor admits a prorepresentation. -/
  isProrepresentable_R : Functor.IsProrepresentable R

/-- Two prorepresentable functors form a prorepresentable pair. -/
instance instIsProrepresentableFunctors
    (U R : ArtinianLocalAlgCat Λ k ⥤ Type u)
    [Functor.IsProrepresentable U] [Functor.IsProrepresentable R] :
    IsProrepresentableFunctors U R where
  isProrepresentable_U := inferInstance
  isProrepresentable_R := inferInstance

/-- Prorepresentability of a groupoid means prorepresentability of both its functors. -/
abbrev IsProrepresentable
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k)) : Prop :=
  IsProrepresentableFunctors G.U G.R

/-- The object functor of a prorepresentable pair is prorepresentable. -/
theorem isProrepresentableFunctors_U (U R : ArtinianLocalAlgCat Λ k ⥤ Type u)
    [h : IsProrepresentableFunctors U R] : Functor.IsProrepresentable U :=
  h.isProrepresentable_U

/-- The arrow functor of a prorepresentable pair is prorepresentable. -/
theorem isProrepresentableFunctors_R (U R : ArtinianLocalAlgCat Λ k ⥤ Type u)
    [h : IsProrepresentableFunctors U R] : Functor.IsProrepresentable R :=
  h.isProrepresentable_R

/-- A groupoid is prorepresentable exactly when both structure functors are. -/
theorem isProrepresentable_iff
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k)) :
    IsProrepresentable G ↔
      Functor.IsProrepresentable G.U ∧ Functor.IsProrepresentable G.R :=
  ⟨fun h ↦ ⟨h.isProrepresentable_U, h.isProrepresentable_R⟩,
    fun h ↦ ⟨h.1, h.2⟩⟩

/-- A prorepresentable groupoid has prorepresentable object and arrow functors. -/
theorem isProrepresentable_spec
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [h : IsProrepresentable G] :
    Functor.IsProrepresentable G.U ∧ Functor.IsProrepresentable G.R :=
  ⟨h.isProrepresentable_U, h.isProrepresentable_R⟩

/-- Two restricted coyoneda functors form a prorepresentable pair. -/
instance instIsProrepresentableFunctorsRestrictedCoyoneda
    (A B : CompleteLocalAlgCat Λ k) :
    IsProrepresentableFunctors (CompleteLocalAlgCat.restrictedCoyoneda A)
      (CompleteLocalAlgCat.restrictedCoyoneda B) where
  isProrepresentable_U := Functor.instIsProrepresentableRestrictedCoyoneda A
  isProrepresentable_R := Functor.instIsProrepresentableRestrictedCoyoneda B

noncomputable section

open Limits Opposite

/-- Restriction of a groupoid in functors on complete local algebras along the
inclusion of Artinian local algebras. -/
def restrictInclusion
    (Ghat : GroupoidInFunctors.{u + 1, u, u} (CompleteLocalAlgCat Λ k)) :
    GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k) :=
  restrict.{u + 1, u + 1, u, u, u} Ghat ArtinianLocalAlgCat.inclusion

/-- Restriction along the inclusion precomposes the object functor with the
inclusion of Artinian local algebras. -/
theorem restrictInclusion_U
    (Ghat : GroupoidInFunctors.{u + 1, u, u} (CompleteLocalAlgCat Λ k)) :
    (restrictInclusion Ghat).U = ArtinianLocalAlgCat.inclusion ⋙ Ghat.U :=
  sorry

/-- Restriction along the inclusion precomposes the arrow functor with the
inclusion of Artinian local algebras. -/
theorem restrictInclusion_R
    (Ghat : GroupoidInFunctors.{u + 1, u, u} (CompleteLocalAlgCat Λ k)) :
    (restrictInclusion Ghat).R = ArtinianLocalAlgCat.inclusion ⋙ Ghat.R :=
  sorry

/-- A groupoid in functors on Artinian local algebras is prorepresentable exactly
when it is isomorphic to the restriction of a representable groupoid in functors
on complete local algebras. -/
theorem isProrepresentable_iff_restriction
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k)) :
    IsProrepresentable G ↔
      ∃ Ghat : GroupoidInFunctors.{u + 1, u, u} (CompleteLocalAlgCat Λ k),
        IsRepresentable Ghat ∧ Nonempty (Iso (restrictInclusion Ghat) G) :=
  sorry

/-- The restriction of a representable groupoid in functors on complete local
algebras is prorepresentable. -/
theorem isProrepresentable_restrict
    (Ghat : GroupoidInFunctors.{u + 1, u, u} (CompleteLocalAlgCat Λ k))
    [IsRepresentable Ghat] : IsProrepresentable (restrictInclusion Ghat) :=
  (isProrepresentable_iff_restriction (restrictInclusion Ghat)).mpr
    ⟨Ghat, inferInstance, ⟨Iso.refl (restrictInclusion Ghat)⟩⟩

/-- A groupoid in functors on Artinian local algebras is prorepresentable exactly
when it is isomorphic to a restricted coyoneda groupoid with representing objects,
source and target morphisms with a pushout, composition, identity and inverse
maps, and groupoid laws. -/
theorem isProrepresentable_iff_coyoneda
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k)) :
    IsProrepresentable G ↔
      ∃ (R0 R1 : CompleteLocalAlgCat Λ k) (src tgt : R0 ⟶ R1)
        (hpush : HasPushout src tgt)
        (comp : R1 ⟶ @pushout (CompleteLocalAlgCat Λ k) _ R0 R1 R1 src tgt hpush)
        (idMap : coyoneda.obj (op R0) ⟶ coyoneda.obj (op R1))
        (invMap : coyoneda.obj (op R1) ⟶ coyoneda.obj (op R1))
        (laws : @CoyonedaGroupoidLaws (CompleteLocalAlgCat Λ k) _ R0 R1 src tgt hpush
          comp idMap invMap),
        Nonempty
          (Iso
            (restrictInclusion
              (@ofCoyoneda (CompleteLocalAlgCat Λ k) _ R0 R1 src tgt hpush
                comp idMap invMap laws))
            G) :=
  sorry

/-- Prorepresentability is invariant under isomorphism of groupoids in functors
on Artinian local algebras. -/
theorem isProrepresentable_of_iso
    {G H : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k)}
    (e : Iso G H) [IsProrepresentable G] : IsProrepresentable H :=
  sorry

end

end Prorepresentable

end CategoryTheory.GroupoidInFunctors
