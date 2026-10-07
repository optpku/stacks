module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.CategoryTheory.Category.ULift

public section

open CategoryTheory CategoryTheory.Functor

universe u v

noncomputable section

namespace PresheafOfModules.ChangeOfRings

variable {C : Type u} [Category.{v} C]
variable (R : Cᵒᵖ ⥤ RingCat.{max u v})

/-- Reindexing to the canonical small category and back preserves module presheaves. -/
private theorem asSmallForwardBackward :
    pushforward₀.{max u v} (AsSmall.down : AsSmall.{0} C ⥤ C) R ⋙
      pushforward₀ AsSmall.up (AsSmall.down.op ⋙ R) = 𝟭 (PresheafOfModules R) := sorry

/-- Reindexing back from the canonical small category and forward preserves module presheaves. -/
private theorem asSmallBackwardForward :
    pushforward₀.{max u v} AsSmall.up (AsSmall.down.op ⋙ R) ⋙
      pushforward₀ (AsSmall.down : AsSmall.{0} C ⥤ C) R =
        𝟭 (PresheafOfModules (AsSmall.down.op ⋙ R)) := sorry

/-- Module presheaves are equivalent to their reindexing on the canonical small category. -/
def asSmallEquivalence :
    PresheafOfModules.{max u v} R ≌
      PresheafOfModules.{max u v} (AsSmall.down.op ⋙ R) :=
  CategoryTheory.Equivalence.mk (pushforward₀ (AsSmall.down : AsSmall.{0} C ⥤ C) R)
    (pushforward₀ AsSmall.up (AsSmall.down.op ⋙ R))
    (eqToIso (asSmallForwardBackward R).symm) (eqToIso (asSmallBackwardForward R))

variable {R} {R' : Cᵒᵖ ⥤ RingCat.{max u v}} (α : R ⟶ R')

/-- Reindexed scalar restriction agrees with scalar restriction on the original category. -/
private theorem asSmallRestrictScalars_eq :
    pushforward₀.{max u v} (AsSmall.down : AsSmall.{0} C ⥤ C) R' ⋙
      (pushforward (F := 𝟭 (AsSmall.{0} C)) (whiskerLeft AsSmall.down.op α) ⋙
        pushforward₀ AsSmall.up (AsSmall.down.op ⋙ R)) = restrictScalars α := sorry

/-- Extension of scalars on a possibly large indexing category, transported from its
canonical small-category presentation. -/
def extendScalars : PresheafOfModules.{max u v} R ⥤ PresheafOfModules.{max u v} R' :=
  ((asSmallEquivalence R).functor ⋙
    pullback (F := 𝟭 (AsSmall.{0} C))
      (R := (AsSmall.down : AsSmall.{0} C ⥤ C).op ⋙ R')
      (whiskerLeft (AsSmall.down : AsSmall.{0} C ⥤ C).op α)) ⋙
      (asSmallEquivalence R').inverse

/-- Extension and restriction of scalars on module presheaves form an adjunction. -/
def extendRestrictAdjunction : extendScalars α ⊣ restrictScalars α :=
  (((asSmallEquivalence R).toAdjunction.comp
    (pullbackPushforwardAdjunction (F := 𝟭 (AsSmall.{0} C))
      (R := (AsSmall.down : AsSmall.{0} C ⥤ C).op ⋙ R')
      (whiskerLeft (AsSmall.down : AsSmall.{0} C ⥤ C).op α))).comp
        (asSmallEquivalence R').symm.toAdjunction).ofNatIsoRight
          (eqToIso (asSmallRestrictScalars_eq α))

/-- Restriction of scalars on module presheaves is a right adjoint. -/
instance restrictScalarsIsRightAdjoint : (restrictScalars.{max u v} α).IsRightAdjoint :=
  ⟨⟨extendScalars α, ⟨extendRestrictAdjunction α⟩⟩⟩

/-- Identity-site pushforward along a coefficient morphism is a right adjoint. -/
instance pushforwardOverIdIsRightAdjoint :
    (pushforward.{max u v} (F := 𝟭 C) α).IsRightAdjoint :=
  Functor.isRightAdjoint_of_iso (Iso.refl (restrictScalars.{max u v} α))

end PresheafOfModules.ChangeOfRings
