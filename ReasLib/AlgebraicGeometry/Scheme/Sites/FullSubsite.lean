module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.CommRing
public import Mathlib.AlgebraicGeometry.AffineSpace
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.LowerShriek.Basic

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.StandardTopology

/-- A full subcategory of the big `τ`-site that contains the terminal object and is closed under
ambient covering families and product over the base with the affine line. -/
class IsFullSubsite (τ : StandardTopology) (X : Scheme.{u})
    (P : ObjectProperty (Over X)) : Prop where
  closedUnderCoverings : ∀ {ι : Type u} {U : Over X}
    (V : ι → Over X) (f : ∀ i, V i ⟶ U), P U →
      Presieve.ofArrows V f ∈ X.overPretopology
        (StandardTopology.Small.morphismProperty τ) U → ∀ i, P (V i)
  affineLine {U : Over X} : P U →
    P (Over.mk (pullback.fst U.hom
      (AffineSpace (ULift.{u} (Fin 1)) X ↘ X) ≫ U.hom))
  terminal : P (Over.mk (𝟙 X))

/-- The whole big `τ`-site contains the terminal object and is closed under coverings and
products over the base with the affine line. -/
instance isFullSubsite_top (τ : StandardTopology) (X : Scheme.{u}) :
    IsFullSubsite τ X (⊤ : ObjectProperty (Over X)) := sorry

/-- A full subcategory is a full subsite exactly when it is closed under ambient covering
families and affine-line products and contains the terminal object. -/
theorem isFullSubsite_iff (τ : StandardTopology) (X : Scheme.{u})
    (P : ObjectProperty (Over X)) :
    IsFullSubsite τ X P ↔
      (∀ {ι : Type u} {U : Over X} (V : ι → Over X) (f : ∀ i, V i ⟶ U),
        P U → Presieve.ofArrows V f ∈ X.overPretopology
          (StandardTopology.Small.morphismProperty τ) U →
          ∀ i, P (V i)) ∧
      (∀ {U : Over X}, P U →
        P (Over.mk (pullback.fst U.hom
          (AffineSpace (ULift.{u} (Fin 1)) X ↘ X) ≫ U.hom))) ∧
      P (Over.mk (𝟙 X)) := sorry

/-- Inclusion of a full subsite into the big site is continuous. -/
instance fullSubsiteToBigSiteContinuous (τ : StandardTopology) (X : Scheme.{u})
    (P : ObjectProperty (Over X)) [IsFullSubsite τ X P] :
    P.ι.IsContinuous (P.ι.restrictedTopology (τ.overTopology X)) (τ.overTopology X) := sorry

/-- The commutative structure sheaf restricted to a full subsite. -/
noncomputable def IsFullSubsite.structureSheaf (τ : StandardTopology) (X : Scheme.{u})
    (P : ObjectProperty (Over X)) [IsFullSubsite τ X P] :
    Sheaf (P.ι.restrictedTopology (τ.overTopology X)) CommRingCat.{u + 1} :=
  (P.ι.sheafPushforwardContinuous CommRingCat.{u + 1}
    (P.ι.restrictedTopology (τ.overTopology X)) (τ.overTopology X)).obj
      (Scheme.AssociatedModule.bigCommStructureSheaf τ X)

/-- The underlying presheaf of the restricted structure sheaf is the restriction of the
ambient structure presheaf. -/
theorem IsFullSubsite.structureSheaf_obj (τ : StandardTopology) (X : Scheme.{u})
    (P : ObjectProperty (Over X)) [IsFullSubsite τ X P] :
    (IsFullSubsite.structureSheaf τ X P).obj =
      P.ι.op ⋙ (Scheme.AssociatedModule.bigCommStructureSheaf τ X).obj := sorry

/-- The canonical map from the structure sheaf on the smaller full subsite to the restriction of
the structure sheaf on the larger one. -/
noncomputable def IsFullSubsite.structureSheafRestriction
    (τ : StandardTopology) (X : Scheme.{u})
    (P₁ P₂ : ObjectProperty (Over X)) [IsFullSubsite τ X P₁] [IsFullSubsite τ X P₂]
    (hP : P₁ ≤ P₂)
    [(P₁.ιOfLE hP).IsContinuous
      (P₁.ι.restrictedTopology (τ.overTopology X))
      (P₂.ι.restrictedTopology (τ.overTopology X))] :
    IsFullSubsite.structureSheaf τ X P₁ ⟶
      ((P₁.ιOfLE hP).sheafPushforwardContinuous CommRingCat.{u + 1}
        (P₁.ι.restrictedTopology (τ.overTopology X))
        (P₂.ι.restrictedTopology (τ.overTopology X))).obj
          (IsFullSubsite.structureSheaf τ X P₂) where
  hom := 𝟙 _

/-- The underlying natural transformation of the structure-sheaf restriction map is the
identity. -/
theorem IsFullSubsite.structureSheafRestriction_hom
    (τ : StandardTopology) (X : Scheme.{u})
    (P₁ P₂ : ObjectProperty (Over X)) [IsFullSubsite τ X P₁] [IsFullSubsite τ X P₂]
    (hP : P₁ ≤ P₂)
    [(P₁.ιOfLE hP).IsContinuous
      (P₁.ι.restrictedTopology (τ.overTopology X))
      (P₂.ι.restrictedTopology (τ.overTopology X))] :
    (IsFullSubsite.structureSheafRestriction τ X P₁ P₂ hP).hom = 𝟙 _ := sorry

/-- The inclusion of nested full subcategories is fully faithful. -/
def fullSubsiteInclusionFullyFaithful {X : Scheme.{u}}
    {P₁ P₂ : ObjectProperty (Over X)} (hP : P₁ ≤ P₂) :
    (P₁.ιOfLE hP).FullyFaithful :=
  CategoryTheory.ObjectProperty.fullyFaithfulιOfLE hP

section Nested

variable (τ : StandardTopology) (X : Scheme.{u})
variable (P₁ P₂ : ObjectProperty (Over X)) [IsFullSubsite τ X P₁] [IsFullSubsite τ X P₂]
variable (hP : P₁ ≤ P₂)

/-- The inclusion of nested full subsites is continuous for the restricted topologies. -/
instance fullSubsiteInclusionContinuous :
    (P₁.ιOfLE hP).IsContinuous
      (P₁.ι.restrictedTopology (τ.overTopology X))
      (P₂.ι.restrictedTopology (τ.overTopology X)) := sorry

/-- The inclusion of nested full subsites is cocontinuous for the restricted topologies. -/
instance fullSubsiteInclusionCocontinuous :
    (P₁.ιOfLE hP).IsCocontinuous
      (P₁.ι.restrictedTopology (τ.overTopology X))
      (P₂.ι.restrictedTopology (τ.overTopology X)) := sorry

/-- The canonical additive lower-shriek map between the restricted structure sheaves,
adjoint to the structure-sheaf restriction map. -/
noncomputable def IsFullSubsite.lowerShriekStructureSheafMap :
    ((P₁.ιOfLE hP).sheafPullback AddCommGrpCat.{u + 1}
      (P₁.ι.restrictedTopology (τ.overTopology X))
      (P₂.ι.restrictedTopology (τ.overTopology X))).obj
        ((sheafCompose (P₁.ι.restrictedTopology (τ.overTopology X))
          (forget₂ CommRingCat.{u + 1} RingCat ⋙
            forget₂ RingCat AddCommGrpCat)).obj
            (IsFullSubsite.structureSheaf τ X P₁)) ⟶
      (sheafCompose (P₂.ι.restrictedTopology (τ.overTopology X))
        (forget₂ CommRingCat.{u + 1} RingCat ⋙
          forget₂ RingCat AddCommGrpCat)).obj
          (IsFullSubsite.structureSheaf τ X P₂) :=
  (((P₁.ιOfLE hP).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (P₁.ι.restrictedTopology (τ.overTopology X))
    (P₂.ι.restrictedTopology (τ.overTopology X))).homEquiv _ _).symm
      ((sheafCompose (P₁.ι.restrictedTopology (τ.overTopology X))
        (forget₂ CommRingCat.{u + 1} RingCat ⋙
          forget₂ RingCat AddCommGrpCat)).map
          (IsFullSubsite.structureSheafRestriction τ X P₁ P₂ hP))

/-- The canonical map from lower shriek of the structure sheaf on the smaller full subsite
to the structure sheaf on the larger full subsite is an isomorphism. -/
@[instance]
theorem lowerShriekStructureSheafMap_isIso :
    IsIso (IsFullSubsite.lowerShriekStructureSheafMap τ X P₁ P₂ hP) := sorry

end Nested

end AlgebraicGeometry.StandardTopology
