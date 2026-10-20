module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StrictTransform.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback

/-!
# Strict transforms along blowups

The strict transform of an algebraic space is its blowup in the inverse-image
center. Module strict transforms agree with relative strict transforms through
the canonical quotient maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The strict transform along a blowup is the blowup in the inverse-image center. -/
@[stacks 0864]
theorem strictTransformFst_isBlowup {S : Scheme.{u}} {B B' X : AlgebraicSpace S}
    (Z : ClosedSubspace B) (b : B' ⟶ B) [IsBlowup b Z] (f : X ⟶ B)
    [QuasiCompact (strictTransformOpenComplement b (Z.inverseImageSubspace b) f).ι] :
    IsBlowup (strictTransformFst b (Z.inverseImageSubspace b) f)
      (Z.inverseImageSubspace f) :=
  sorry

/-- The relative strict-transform quotient, transported by pullback composition
and transposed along the canonical comparison morphism of ambient spaces. -/
def strictTransformRelativeπ {S : Scheme.{u}} {B B' X : AlgebraicSpace S}
    (Z : ClosedSubspace B) (b : B' ⟶ B) (f : X ⟶ B)
    [QuasiCompact (strictTransformOpenComplement b (Z.inverseImageSubspace b) f).ι]
    (F : X.Modules) :
    (strictTransformPullbackFunctor b f).obj F ⟶
      (Modules.pushforward
        (strictTransformRelativeMap b (Z.inverseImageSubspace b) f)).obj
        (strictTransformModule
          (strictTransformFst b (Z.inverseImageSubspace b) f)
          ((Z.inverseImageSubspace f).inverseImageSubspace
            (strictTransformFst b (Z.inverseImageSubspace b) f))
          (𝟙 X) F) := by
  let E := Z.inverseImageSubspace b
  let p := strictTransformFst b E f
  let D := (Z.inverseImageSubspace f).inverseImageSubspace p
  let m := strictTransformRelativeMap b E f
  let r := pullback.fst f b
  let s := pullback.fst (𝟙 X) p
  have h : m ≫ r = s := strictTransformRelativeMap_fst b E f
  exact (Modules.pullbackPushforwardAdjunction m).homEquiv _ _
    ((Modules.pullbackCompIso m r).hom.app F ≫
      eqToHom (congrArg (fun q ↦ (Modules.pullback q).obj F) h) ≫
      strictTransformπ p D (𝟙 X) F)

/-- The strict transform of a quasi-coherent module along a blowup is isomorphic
to the pushforward of its relative strict transform, compatibly with the
canonical quotient maps. -/
@[stacks 0864]
theorem strictTransformModule_isomorphic_pushforward_relativeStrictTransform
    {S : Scheme.{u}} {B B' X : AlgebraicSpace S}
    (Z : ClosedSubspace B) (b : B' ⟶ B) [IsBlowup b Z] (f : X ⟶ B)
    [QuasiCompact (strictTransformOpenComplement b (Z.inverseImageSubspace b) f).ι]
    (F : X.Modules) [F.IsQuasicoherent] :
    ∃ e : strictTransformModule b (Z.inverseImageSubspace b) f F ≅
      (Modules.pushforward
        (strictTransformRelativeMap b (Z.inverseImageSubspace b) f)).obj
        (strictTransformModule
          (strictTransformFst b (Z.inverseImageSubspace b) f)
          ((Z.inverseImageSubspace f).inverseImageSubspace
            (strictTransformFst b (Z.inverseImageSubspace b) f))
          (𝟙 X) F),
      strictTransformπ b (Z.inverseImageSubspace b) f F ≫ e.hom =
        strictTransformRelativeπ Z b f F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
