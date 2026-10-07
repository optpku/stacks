module

public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap109.Lemma_109_9_1_Substack

/-!
# The object property of smooth curves with universally trivial pushforward of 𝒪

`𝒞urves^{smooth, h0}` is the full subcategory of families of curves that are
smooth and lie in `𝒞urves^{h0, 1}`. Membership is the source-facing packaging
of a classifying morphism factoring through that open substack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- The object property of smooth families of curves with universally trivial
`𝒪_S ⟶ f_* 𝒪_X` and fibres of dimension `1`, corresponding to the open
substack `𝒞urves^{smooth, h0}`. -/
def smoothH0 (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦ AlgebraicSpace.Smooth (hom P) ∧ h0Dim1 S P

/-- Membership in `smoothH0` means `𝒪_S ⟶ f_* 𝒪_X` is an isomorphism after
every base change, including the identity, and the structure morphism is
smooth of relative dimension `1`. -/
theorem smoothH0_iff {S : Scheme.{u}} (P : Obj S) :
    smoothH0 S P ↔
      (∀ {Z : AlgebraicSpace S} (g : Z ⟶ ofOver (base P)),
          IsIso (Modules.unitToPushforwardObjUnit (pullback.snd (hom P) g))) ∧
        AlgebraicSpace.Smooth (hom P) ∧ RelativeDimension (hom P) 1 :=
  sorry

/-- The `smoothH0` property of families of curves is closed under
isomorphisms. -/
instance instIsClosedUnderIsomorphisms_smoothH0 (S : Scheme.{u}) :
    (smoothH0 S).IsClosedUnderIsomorphisms :=
  sorry

/-- Membership in `𝒞urves^{smooth, h0}` implies membership in
`𝒞urves^{h0, 1}`. -/
theorem smoothH0_le_h0Dim1 {S : Scheme.{u}} (P : Obj S) :
    smoothH0 S P → h0Dim1 S P :=
  sorry

/-- Membership in `𝒞urves^{smooth, h0}` implies smoothness of the structure
morphism. -/
theorem smoothH0_smooth {S : Scheme.{u}} (P : Obj S) :
    smoothH0 S P → AlgebraicSpace.Smooth (hom P) :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
