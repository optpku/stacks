module

public import Mathlib.Data.List.TFAE
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Basic
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.Etale
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Proper

/-!
# Local tests for proper morphisms of formal algebraic spaces

Properness of a morphism of formal algebraic spaces is equivalent to
properness after scheme or affine base change, algebraic-space properness
of affine pullbacks, and properness over an affine formal étale atlas.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

namespace Proper

variable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y)

/-- The projection of every scheme-valued base change of `f` is proper. -/
def forallScheme : Prop :=
  ∀ {Z : Over S} {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj Z ⟶ Y}
    {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Proper pZ

/-- `forallScheme f` means every scheme-valued pullback projection of `f` is
proper. -/
theorem forallScheme_iff : forallScheme f ↔
    ∀ (Z : Over S) (P : (Over S)ᵒᵖ ⥤ Type u) (g : yoneda.obj Z ⟶ Y)
      (pZ : P ⟶ yoneda.obj Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → Proper pZ := sorry

namespace forallScheme

/-- A universal scheme-valued pullback condition witnesses `forallScheme f`. -/
theorem of (h : ∀ {Z : Over S} {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj Z ⟶ Y}
    {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Proper pZ) : forallScheme f := sorry

/-- Under `forallScheme f`, the test-leg of any scheme-valued pullback of `f` is
proper. -/
theorem spec (h : forallScheme f) {Z : Over S} {P : (Over S)ᵒᵖ ⥤ Type u}
    {g : yoneda.obj Z ⟶ Y} {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : Proper pZ := sorry

/-- The chosen pullback projection `pullback.snd f g` along a morphism from a
scheme is proper whenever `forallScheme f` holds. -/
theorem pullback_snd {Z : Over S} (h : forallScheme f) (g : yoneda.obj Z ⟶ Y)
    [HasPullback f g] : Proper (pullback.snd f g) := sorry

end forallScheme

/-- The projection of every affine-scheme-valued base change of `f` is proper. -/
def forallAffine : Prop :=
  ∀ {Z : Over S} [AlgebraicGeometry.IsAffine Z.left] {P : (Over S)ᵒᵖ ⥤ Type u}
    {g : yoneda.obj Z ⟶ Y} {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Proper pZ

/-- `forallAffine f` means every affine-scheme-valued pullback projection of `f`
is proper. -/
theorem forallAffine_iff : forallAffine f ↔
    ∀ (Z : Over S) [AlgebraicGeometry.IsAffine Z.left]
      (P : (Over S)ᵒᵖ ⥤ Type u) (g : yoneda.obj Z ⟶ Y)
      (pZ : P ⟶ yoneda.obj Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → Proper pZ := sorry

namespace forallAffine

/-- A universal affine-scheme-valued pullback condition witnesses
`forallAffine f`. -/
theorem of (h : ∀ {Z : Over S} [AlgebraicGeometry.IsAffine Z.left]
    {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj Z ⟶ Y}
    {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Proper pZ) : forallAffine f := sorry

/-- Under `forallAffine f`, the test-leg of any affine-scheme-valued pullback of
`f` is proper. -/
theorem spec (h : forallAffine f) {Z : Over S} [AlgebraicGeometry.IsAffine Z.left]
    {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj Z ⟶ Y}
    {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : Proper pZ := sorry

/-- The chosen pullback projection `pullback.snd f g` along a morphism from an
affine scheme is proper whenever `forallAffine f` holds. -/
theorem pullback_snd {Z : Over S} [AlgebraicGeometry.IsAffine Z.left]
    (h : forallAffine f) (g : yoneda.obj Z ⟶ Y) [HasPullback f g] :
    Proper (pullback.snd f g) := sorry

end forallAffine

/-- The algebraic-space structure morphism of an affine-scheme-valued base
change of `f`, as the first projection of the fibre product of functors. -/
def affineBaseChangeHom {Z : Over S} [AlgebraicGeometry.IsAffine Z.left]
    (ξ : yoneda.obj Z ⟶ Y) (hξ : AlgebraicSpace.IsAlgebraicSpace (pullback ξ f)) :
    AlgebraicSpace.ofFunctor (pullback ξ f) hξ.isSheaf hξ.representableDiagonal hξ.atlas ⟶
      AlgebraicSpace.ofOver Z :=
  pullback.fst ξ f

/-- The structure morphism of an affine-scheme-valued base change is the first
projection of the fibre product. -/
theorem affineBaseChangeHom_fst {Z : Over S} [AlgebraicGeometry.IsAffine Z.left]
    (ξ : yoneda.obj Z ⟶ Y) (hξ : AlgebraicSpace.IsAlgebraicSpace (pullback ξ f)) :
    affineBaseChangeHom f ξ hξ = pullback.fst ξ f := sorry

/-- Every affine-scheme-valued fibre product of `f` is an algebraic space proper
over the affine scheme. -/
def forallAffineAlgebraicSpace : Prop :=
  ∀ {Z : Over S} [AlgebraicGeometry.IsAffine Z.left] (ξ : yoneda.obj Z ⟶ Y),
    ∃ hξ, AlgebraicSpace.Proper (affineBaseChangeHom f ξ hξ)

/-- `forallAffineAlgebraicSpace f` means every affine-scheme-valued fibre
product of `f` is an algebraic space proper over the affine scheme. -/
theorem forallAffineAlgebraicSpace_iff : forallAffineAlgebraicSpace f ↔
    ∀ (Z : Over S) [AlgebraicGeometry.IsAffine Z.left] (ξ : yoneda.obj Z ⟶ Y),
      ∃ hξ, AlgebraicSpace.Proper (affineBaseChangeHom f ξ hξ) := sorry

namespace forallAffineAlgebraicSpace

/-- Affine-scheme-valued algebraic-space pullbacks that are proper over the
affine scheme witness `forallAffineAlgebraicSpace f`. -/
theorem of
    (h : ∀ {Z : Over S} [AlgebraicGeometry.IsAffine Z.left]
      (ξ : yoneda.obj Z ⟶ Y),
      ∃ hξ, AlgebraicSpace.Proper (affineBaseChangeHom f ξ hξ)) :
    forallAffineAlgebraicSpace f := sorry

/-- `forallAffineAlgebraicSpace f` supplies, for every affine scheme morphism to
`Y`, an algebraic-space structure on the fibre product together with properness
of the structure morphism. -/
theorem spec (h : forallAffineAlgebraicSpace f) {Z : Over S}
    [AlgebraicGeometry.IsAffine Z.left] (ξ : yoneda.obj Z ⟶ Y) :
    ∃ hξ, AlgebraicSpace.Proper (affineBaseChangeHom f ξ hξ) := sorry

/-- Under `forallAffineAlgebraicSpace f`, every affine-scheme-valued fibre
product of `f` is an algebraic space. -/
theorem isAlgebraicSpace (h : forallAffineAlgebraicSpace f) {Z : Over S}
    [AlgebraicGeometry.IsAffine Z.left] (ξ : yoneda.obj Z ⟶ Y) :
    AlgebraicSpace.IsAlgebraicSpace (pullback ξ f) := sorry

/-- Under `forallAffineAlgebraicSpace f`, the structure morphism of an
affine-scheme-valued algebraic-space fibre product is proper. -/
theorem proper (h : forallAffineAlgebraicSpace f) {Z : Over S}
    [AlgebraicGeometry.IsAffine Z.left] (ξ : yoneda.obj Z ⟶ Y)
    (hξ : AlgebraicSpace.IsAlgebraicSpace (pullback ξ f)) :
    AlgebraicSpace.Proper (affineBaseChangeHom f ξ hξ) := sorry

end forallAffineAlgebraicSpace

/-- There is a covering of `Y` by directed affine thickening colimits,
étale and jointly fppf-locally surjective, along which every pullback
of `f` is proper. -/
def existsCoverOnTarget : Prop :=
  ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (j : ι) → Y_ j ⟶ Y),
    (∀ j, ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
      (D : Λ ⥤ Over S), IsDirectedAffineThickeningColimit D (Y_ j)) ∧
      (∀ j, Etale (π j)) ∧
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) ∧
          (∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
            IsPullback pY pX (π j) f → Proper pY)

/-- `existsCoverOnTarget f` means that `Y` has an étale, jointly
fppf-locally surjective atlas by directed affine thickening colimits
along which pullbacks of `f` are proper. -/
theorem existsCoverOnTarget_iff : existsCoverOnTarget f ↔
    ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (j : ι) → Y_ j ⟶ Y),
      (∀ j, ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
        (D : Λ ⥤ Over S), IsDirectedAffineThickeningColimit D (Y_ j)) ∧
        (∀ j, Etale (π j)) ∧
          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
            (sigmaDesc π) ∧
            (∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
              IsPullback pY pX (π j) f → Proper pY) := sorry

namespace existsCoverOnTarget

/-- An étale, jointly fppf-locally surjective atlas of `Y` by directed
affine thickening colimits with proper pullbacks of `f` witnesses
`existsCoverOnTarget f`. -/
theorem of {ι : Type u} {Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)}
    (π : (j : ι) → Y_ j ⟶ Y)
    (hAffine : ∀ j, ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
      (D : Λ ⥤ Over S), IsDirectedAffineThickeningColimit D (Y_ j))
    (hEtale : ∀ j, Etale (π j))
    (hCover : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (sigmaDesc π))
    (hProper : ∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
      IsPullback pY pX (π j) f → Proper pY) :
    existsCoverOnTarget f := sorry

/-- `existsCoverOnTarget f` supplies an étale, jointly fppf-locally
surjective atlas of `Y` by directed affine thickening colimits along
which pullbacks of `f` are proper. -/
theorem spec (h : existsCoverOnTarget f) :
    ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (j : ι) → Y_ j ⟶ Y),
      (∀ j, ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
        (D : Λ ⥤ Over S), IsDirectedAffineThickeningColimit D (Y_ j)) ∧
        (∀ j, Etale (π j)) ∧
          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
            (sigmaDesc π) ∧
            (∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
              IsPullback pY pX (π j) f → Proper pY) := sorry

end existsCoverOnTarget

/-- For a morphism of formal algebraic spaces, properness is equivalent to
properness after every scheme base change, after every affine scheme base
change, to every affine pullback being an algebraic space proper over the
affine scheme, and to properness after pullback along an étale, jointly
fppf-locally surjective atlas by directed affine thickening colimits. -/
theorem tfae [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (f : X ⟶ Y) :
    List.TFAE [Proper f, forallScheme f, forallAffine f,
      forallAffineAlgebraicSpace f, existsCoverOnTarget f] := sorry

/-- A morphism of formal algebraic spaces is proper iff every scheme-valued
base change has proper projection. -/
theorem iff_forallScheme [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (f : X ⟶ Y) : Proper f ↔ forallScheme f := sorry

/-- A morphism of formal algebraic spaces is proper iff every
affine-scheme-valued base change has proper projection. -/
theorem iff_forallAffine [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (f : X ⟶ Y) : Proper f ↔ forallAffine f := sorry

/-- A morphism of formal algebraic spaces is proper iff every
affine-scheme-valued fibre product is an algebraic space proper over the
affine scheme. -/
theorem iff_forallAffineAlgebraicSpace [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (f : X ⟶ Y) :
    Proper f ↔ forallAffineAlgebraicSpace f := sorry

/-- A morphism of formal algebraic spaces is proper iff the target has an
étale, jointly fppf-locally surjective atlas by directed affine thickening
colimits with proper pullbacks. -/
theorem iff_existsCoverOnTarget [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (f : X ⟶ Y) : Proper f ↔ existsCoverOnTarget f := sorry


end Proper

end AlgebraicGeometry.FormalAlgebraicSpace
