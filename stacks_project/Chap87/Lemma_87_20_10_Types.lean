/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Reduced
public import stacks_project.Chap87.Lemma_87_10_3_Types

/-!
# Local types of formal algebraic spaces

A formal algebraic space is locally countably indexed, locally countably
indexed and classical, locally weakly adic, or locally Noetherian when every
representable étale morphism from an affine formal algebraic space has the
corresponding affine type. These are the sheaf-site owners for
Definition 87.20.7, parallel to `IsLocallyAdicStar`.

The sheaf reduction `X_red` is constructed on the `Definition_87_23_2_Formal`
carrier as the coequalizer of the kernel pair of the coproduct of affine
stage reductions of an étale atlas. `Lemma_87_12_1_Reduction` cannot be
imported here, because it duplicates `IsFormalAlgebraicSpace`. Induced maps
of reductions are characterized by the square `φ ≫ reductionι Y = reductionι X ≫ f`
rather than by a chosen witness.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open CategoryTheory.Functor Opposite
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry

/-- A formal algebraic space is locally countably indexed when every morphism
from an affine formal algebraic space that is representable by algebraic
spaces and relatively étale has countably indexed source. -/
class IsLocallyCountablyIndexed {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop
    extends IsFormalAlgebraicSpace X where
  /-- Every representable étale morphism from an affine formal algebraic space
  has countably indexed source. -/
  of_etale_affine :
    ∀ {Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : Y ⟶ X),
      IsAffineFormalAlgebraicSpace Y → representableByAlgebraicSpaces f →
        relativelyEtale f → IsCountablyIndexedAffine Y

namespace IsLocallyCountablyIndexed

/-- A countably indexed affine formal algebraic space is locally countably
indexed. -/
instance ofAffine {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsCountablyIndexedAffine X] : IsLocallyCountablyIndexed X :=
  sorry

/-- A locally countably indexed formal algebraic space has every representable
étale affine chart countably indexed. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsLocallyCountablyIndexed X]
    {Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : Y ⟶ X)
    (hY : IsAffineFormalAlgebraicSpace Y)
    (hrep : representableByAlgebraicSpaces f) (het : relativelyEtale f) :
    IsCountablyIndexedAffine Y :=
  sorry

/-- Locally countably indexed unpacks as a formal algebraic space whose affine
étale atlas objects are countably indexed. -/
theorem iff_atlas {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsLocallyCountablyIndexed X ↔
      IsFormalAlgebraicSpace X ∧
        ∃ (ι : Type (max u v))
          (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
          (π : ∀ i, X_ i ⟶ X) (c : Cofan X_) (hc : IsColimit c),
            (∀ i, IsAffineFormalAlgebraicSpace (X_ i)) ∧
              (∀ i, representableByAlgebraicSpaces (π i)) ∧
                (∀ i, relativelyEtale (π i)) ∧
                  Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π) ∧
                    ∀ i, IsCountablyIndexedAffine (X_ i) :=
  sorry

end IsLocallyCountablyIndexed

/-- A formal algebraic space is locally countably indexed and classical when
every morphism from an affine formal algebraic space that is representable by
algebraic spaces and relatively étale has countably indexed and classical
source. -/
class IsLocallyClassical {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop
    extends IsFormalAlgebraicSpace X where
  /-- Every representable étale morphism from an affine formal algebraic space
  has countably indexed and classical source. -/
  of_etale_affine :
    ∀ {Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : Y ⟶ X),
      IsAffineFormalAlgebraicSpace Y → representableByAlgebraicSpaces f →
        relativelyEtale f → IsCountablyIndexedAffine Y ∧ IsClassicalAffine Y

namespace IsLocallyClassical

/-- A countably indexed classical affine formal algebraic space is locally
countably indexed and classical. -/
instance ofAffine {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsCountablyIndexedAffine X] [IsClassicalAffine X] :
    IsLocallyClassical X :=
  sorry

/-- A locally countably indexed and classical formal algebraic space has every
representable étale affine chart countably indexed and classical. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsLocallyClassical X]
    {Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : Y ⟶ X)
    (hY : IsAffineFormalAlgebraicSpace Y)
    (hrep : representableByAlgebraicSpaces f) (het : relativelyEtale f) :
    IsCountablyIndexedAffine Y ∧ IsClassicalAffine Y :=
  sorry

/-- Locally countably indexed and classical unpacks as a formal algebraic space
whose affine étale atlas objects are countably indexed and classical. -/
theorem iff_atlas {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsLocallyClassical X ↔
      IsFormalAlgebraicSpace X ∧
        ∃ (ι : Type (max u v))
          (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
          (π : ∀ i, X_ i ⟶ X) (c : Cofan X_) (hc : IsColimit c),
            (∀ i, IsAffineFormalAlgebraicSpace (X_ i)) ∧
              (∀ i, representableByAlgebraicSpaces (π i)) ∧
                (∀ i, relativelyEtale (π i)) ∧
                  Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π) ∧
                    ∀ i, IsCountablyIndexedAffine (X_ i) ∧ IsClassicalAffine (X_ i) :=
  sorry

end IsLocallyClassical

namespace IsLocallyCountablyIndexed

/-- A locally countably indexed and classical formal algebraic space is locally
countably indexed. -/
instance of_isLocallyClassical {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsLocallyClassical X] :
    IsLocallyCountablyIndexed X :=
  sorry

end IsLocallyCountablyIndexed

/-- A formal algebraic space is locally weakly adic when every morphism from an
affine formal algebraic space that is representable by algebraic spaces and
relatively étale has weakly adic source. -/
class IsLocallyWeaklyAdic {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop
    extends IsFormalAlgebraicSpace X where
  /-- Every representable étale morphism from an affine formal algebraic space
  has weakly adic source. -/
  of_etale_affine :
    ∀ {Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : Y ⟶ X),
      IsAffineFormalAlgebraicSpace Y → representableByAlgebraicSpaces f →
        relativelyEtale f → IsWeaklyAdicAffine Y

namespace IsLocallyWeaklyAdic

/-- A weakly adic affine formal algebraic space is locally weakly adic. -/
instance ofAffine {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsWeaklyAdicAffine X] :
    IsLocallyWeaklyAdic X :=
  sorry

/-- A locally weakly adic formal algebraic space has every representable étale
affine chart weakly adic. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsLocallyWeaklyAdic X]
    {Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : Y ⟶ X)
    (hY : IsAffineFormalAlgebraicSpace Y)
    (hrep : representableByAlgebraicSpaces f) (het : relativelyEtale f) :
    IsWeaklyAdicAffine Y :=
  sorry

/-- Locally weakly adic unpacks as a formal algebraic space whose affine étale
atlas objects are weakly adic. -/
theorem iff_atlas {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsLocallyWeaklyAdic X ↔
      IsFormalAlgebraicSpace X ∧
        ∃ (ι : Type (max u v))
          (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
          (π : ∀ i, X_ i ⟶ X) (c : Cofan X_) (hc : IsColimit c),
            (∀ i, IsAffineFormalAlgebraicSpace (X_ i)) ∧
              (∀ i, representableByAlgebraicSpaces (π i)) ∧
                (∀ i, relativelyEtale (π i)) ∧
                  Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π) ∧
                    ∀ i, IsWeaklyAdicAffine (X_ i) :=
  sorry

end IsLocallyWeaklyAdic

namespace IsFormalAlgebraicSpace

/-- A formal algebraic space is locally Noetherian when every morphism from an
affine formal algebraic space that is representable by algebraic spaces and
relatively étale has Noetherian source. Nested to avoid clashing with the
scheme class `AlgebraicGeometry.IsLocallyNoetherian`. -/
class IsLocallyNoetherian {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop
    extends IsFormalAlgebraicSpace X where
  /-- Every representable étale morphism from an affine formal algebraic space
  has Noetherian source. -/
  of_etale_affine :
    ∀ {Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : Y ⟶ X),
      IsAffineFormalAlgebraicSpace Y → representableByAlgebraicSpaces f →
        relativelyEtale f → IsNoetherianAffine Y

namespace IsLocallyNoetherian

/-- A Noetherian affine formal algebraic space is locally Noetherian. -/
instance ofAffine {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsNoetherianAffine X] :
    IsLocallyNoetherian X :=
  sorry

/-- A locally Noetherian formal algebraic space has every representable étale
affine chart Noetherian. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsLocallyNoetherian X]
    {Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : Y ⟶ X)
    (hY : IsAffineFormalAlgebraicSpace Y)
    (hrep : representableByAlgebraicSpaces f) (het : relativelyEtale f) :
    IsNoetherianAffine Y :=
  sorry

/-- Locally Noetherian unpacks as a formal algebraic space whose affine étale
atlas objects are Noetherian. -/
theorem iff_atlas {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsLocallyNoetherian X ↔
      IsFormalAlgebraicSpace X ∧
        ∃ (ι : Type (max u v))
          (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
          (π : ∀ i, X_ i ⟶ X) (c : Cofan X_) (hc : IsColimit c),
            (∀ i, IsAffineFormalAlgebraicSpace (X_ i)) ∧
              (∀ i, representableByAlgebraicSpaces (π i)) ∧
                (∀ i, relativelyEtale (π i)) ∧
                  Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π) ∧
                    ∀ i, IsNoetherianAffine (X_ i) :=
  sorry

end IsLocallyNoetherian

/-- The reduction of a scheme over a base, as an object of the slice. -/
def schemeSliceReduction {T : Scheme.{u}} (Y : Over T) : Over T :=
  Over.mk (Scheme.reductionι Y.left ≫ Y.hom)

/-- `schemeSliceReduction Y` is the slice object of the scheme-theoretic
reduction of `Y`. -/
theorem schemeSliceReduction_left {T : Scheme.{u}} (Y : Over T) :
    (schemeSliceReduction Y).left = Scheme.reduction Y.left :=
  sorry

/-- The canonical thickening from the slice reduction of a scheme over a
base. -/
def schemeSliceReductionι {T : Scheme.{u}} (Y : Over T) :
    schemeSliceReduction Y ⟶ Y :=
  Over.homMk (Scheme.reductionι Y.left) sorry

/-- The underlying morphism of `schemeSliceReductionι Y` is the
scheme-theoretic reduction inclusion. -/
theorem schemeSliceReductionι_left {T : Scheme.{u}} (Y : Over T) :
    (schemeSliceReductionι Y).left = Scheme.reductionι Y.left :=
  sorry

/-- The sheaf on `(Sch/S)_fppf` associated to a scheme over the image of `S`,
obtained by sheafifying Hom-spaces in the slice and lifting to
`Type (max u v)`. -/
def sheafifySlice {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (Y : Over (𝒮.toScheme.obj S)) :
    Sheaf (𝒮.bigTopology S) (Type (max u v)) :=
  (presheafToSheaf (𝒮.bigTopology S) (Type (max u v))).obj
    ((Over.post 𝒮.toScheme).op ⋙ yoneda.obj Y ⋙ uliftFunctor.{v})

/-- `sheafifySlice Y` is the sheafification of the `ULift` of Hom-spaces in the
slice along `Over.post 𝒮.toScheme`. -/
theorem sheafifySlice_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (Y : Over (𝒮.toScheme.obj S)) :
    sheafifySlice Y =
      (presheafToSheaf (𝒮.bigTopology S) (Type (max u v))).obj
        ((Over.post 𝒮.toScheme).op ⋙ yoneda.obj Y ⋙ uliftFunctor.{v}) :=
  sorry

/-- The sheaf map associated to a morphism of slice schemes. -/
def sheafifySliceMap {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {Y Z : Over (𝒮.toScheme.obj S)} (f : Y ⟶ Z) :
    sheafifySlice Y ⟶ sheafifySlice Z :=
  (presheafToSheaf (𝒮.bigTopology S) (Type (max u v))).map
    (whiskerRight (whiskerLeft (Over.post 𝒮.toScheme).op (yoneda.map f))
      uliftFunctor.{v})

/-- `sheafifySliceMap f` is the sheafification of whiskered Yoneda of `f`. -/
theorem sheafifySliceMap_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {Y Z : Over (𝒮.toScheme.obj S)} (f : Y ⟶ Z) :
    sheafifySliceMap f =
      (presheafToSheaf (𝒮.bigTopology S) (Type (max u v))).map
        (whiskerRight (whiskerLeft (Over.post 𝒮.toScheme).op (yoneda.map f))
          uliftFunctor.{v}) :=
  sorry

/-- Presheaf comparison from slice Yoneda of a site object to `uliftYoneda`. -/
def sliceToUliftYoneda {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    (U : 𝒮.bigSite S) :
    ((Over.post 𝒮.toScheme).op ⋙
        yoneda.obj ((Over.post 𝒮.toScheme).obj U) ⋙ uliftFunctor.{v}) ⟶
      uliftYoneda.{max u v}.obj U where
  app W :=
    ↾fun f ↦
      ULift.up.{max u v, v}
        (Over.homMk (𝒮.fullyFaithful.preimage f.down.left) sorry)
  naturality := sorry

/-- Comparison from the sheafified slice Yoneda of a site object to its
sheafified representable, using full faithfulness of `𝒮.toScheme`. -/
def sliceToSheafifiedRepresentable {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (U : 𝒮.bigSite S) :
    sheafifySlice ((Over.post 𝒮.toScheme).obj U) ⟶
      (𝒮.bigTopology S).sheafifiedRepresentable U :=
  (presheafToSheaf (𝒮.bigTopology S) (Type (max u v))).map (sliceToUliftYoneda U)

/-- `sliceToSheafifiedRepresentable U` is the sheafification of
`sliceToUliftYoneda U`. -/
theorem sliceToSheafifiedRepresentable_spec {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (U : 𝒮.bigSite S) :
    sliceToSheafifiedRepresentable U =
      (presheafToSheaf (𝒮.bigTopology S) (Type (max u v))).map
        (sliceToUliftYoneda U) :=
  sorry

/-- The sheaf associated to the scheme-theoretic reduction of an affine
stage. -/
def affineStageReduction {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {Λ : Type (max u v)} [Preorder Λ] (D : Λ ⥤ 𝒮.bigAffineSite S) (i : Λ) :
    Sheaf (𝒮.bigTopology S) (Type (max u v)) :=
  sheafifySlice
    (schemeSliceReduction
      ((Over.post 𝒮.toScheme).obj ((𝒮.bigAffineInclusion S).obj (D.obj i))))

/-- `affineStageReduction D i` is the sheafified slice of the reduction of the
`i`-th affine stage. -/
theorem affineStageReduction_spec {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {Λ : Type (max u v)} [Preorder Λ] (D : Λ ⥤ 𝒮.bigAffineSite S) (i : Λ) :
    affineStageReduction D i =
      sheafifySlice
        (schemeSliceReduction
          ((Over.post 𝒮.toScheme).obj
            ((𝒮.bigAffineInclusion S).obj (D.obj i)))) :=
  sorry

/-- The stage reduction inclusion into the sheaf colimit of an affine
thickening presentation. -/
def affineStageReductionι {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {Λ : Type (max u v)} [Preorder Λ] (D : Λ ⥤ 𝒮.bigAffineSite S)
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (c : Cocone
      (D ⋙ 𝒮.bigAffineInclusion S ⋙
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor))
    (e : X ≅ c.pt) (i : Λ) : affineStageReduction D i ⟶ X :=
  sheafifySliceMap
      (schemeSliceReductionι
        ((Over.post 𝒮.toScheme).obj ((𝒮.bigAffineInclusion S).obj (D.obj i)))) ≫
    sliceToSheafifiedRepresentable ((𝒮.bigAffineInclusion S).obj (D.obj i)) ≫
    c.ι.app i ≫ e.inv

/-- `affineStageReductionι` is the composite of the slice reduction map, the
comparison to the sheafified representable of the stage, and the cocone
leg. -/
theorem affineStageReductionι_spec {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {Λ : Type (max u v)} [Preorder Λ] (D : Λ ⥤ 𝒮.bigAffineSite S)
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (c : Cocone
      (D ⋙ 𝒮.bigAffineInclusion S ⋙
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor))
    (e : X ≅ c.pt) (i : Λ) :
    affineStageReductionι D c e i =
      sheafifySliceMap
          (schemeSliceReductionι
            ((Over.post 𝒮.toScheme).obj
              ((𝒮.bigAffineInclusion S).obj (D.obj i)))) ≫
        sliceToSheafifiedRepresentable
          ((𝒮.bigAffineInclusion S).obj (D.obj i)) ≫
        c.ι.app i ≫ e.inv :=
  sorry

/-- The chosen directed index of an affine thickening presentation. -/
def affineIndex {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] : Type (max u v) :=
  Classical.choose ‹IsAffineFormalAlgebraicSpace X›.exists_colimit

/-- The chosen preorder on the directed index of an affine thickening
presentation. -/
instance instPreorder_affineIndex {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] : Preorder (affineIndex X) :=
  Classical.choose
    (Classical.choose_spec ‹IsAffineFormalAlgebraicSpace X›.exists_colimit)

/-- The chosen directedness of the index of an affine thickening
presentation. -/
instance instIsDirected_affineIndex {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] : IsDirected (affineIndex X) (· ≤ ·) :=
  Classical.choose
    (Classical.choose_spec
      (Classical.choose_spec ‹IsAffineFormalAlgebraicSpace X›.exists_colimit))

/-- The chosen affine stage diagram of an affine formal algebraic space. -/
def affineDiagram {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    affineIndex X ⥤ 𝒮.bigAffineSite S :=
  Classical.choose
    (Classical.choose_spec
      (Classical.choose_spec
        (Classical.choose_spec ‹IsAffineFormalAlgebraicSpace X›.exists_colimit)))

/-- The chosen diagram is a directed affine thickening colimit of `X`. -/
theorem affineDiagram_isDirectedAffineThickeningColimit
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    IsDirectedAffineThickeningColimit (affineDiagram X) X :=
  Classical.choose_spec
    (Classical.choose_spec
      (Classical.choose_spec
        (Classical.choose_spec ‹IsAffineFormalAlgebraicSpace X›.exists_colimit)))

/-- The chosen sheaf cocone of the affine thickening presentation. -/
def affineCocone {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    Cocone
      (affineDiagram X ⋙ 𝒮.bigAffineInclusion S ⋙
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor) :=
  Classical.choose (affineDiagram_isDirectedAffineThickeningColimit X).2

/-- The chosen cocone is a colimit isomorphic to `X`. -/
theorem affineCocone_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    Nonempty (IsColimit (affineCocone X)) ∧ Nonempty (X ≅ (affineCocone X).pt) :=
  Classical.choose_spec (affineDiagram_isDirectedAffineThickeningColimit X).2

/-- The chosen isomorphism from `X` to the point of the affine thickening
cocone. -/
def affineIso {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] : X ≅ (affineCocone X).pt :=
  Classical.choice (affineCocone_spec X).2

/-- The chosen reduced thickening of an affine formal algebraic space, as the
sheafified reduction of one chosen affine stage together with its structure
morphism, or the identity on `X` when the index is empty. -/
def affineReductionWithι {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    Σ (Y : Sheaf (𝒮.bigTopology S) (Type (max u v))), Y ⟶ X :=
  @dite _ (Nonempty (affineIndex X)) (Classical.propDecidable _)
    (fun h ↦
      ⟨affineStageReduction (affineDiagram X) (Classical.choice h),
        affineStageReductionι (affineDiagram X) (affineCocone X) (affineIso X)
          (Classical.choice h)⟩)
    (fun _ ↦ ⟨X, 𝟙 X⟩)

/-- The reduction of an affine formal algebraic space, as the sheafified
reduction of one chosen affine stage, or `X` itself when the index is
empty. -/
def affineReduction {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    Sheaf (𝒮.bigTopology S) (Type (max u v)) :=
  (affineReductionWithι X).1

/-- The canonical morphism from the affine reduction of an affine formal
algebraic space. -/
def affineReductionι {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    affineReduction X ⟶ X :=
  (affineReductionWithι X).2

/-- The chosen reduced thickening is `affineStageReduction` of the chosen
diagram and stage, or the identity on `X` when that index is empty. -/
theorem affineReductionWithι_spec {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    affineReductionWithι X =
      @dite (Σ (Y : Sheaf (𝒮.bigTopology S) (Type (max u v))), Y ⟶ X)
        (Nonempty (affineIndex X)) (Classical.propDecidable _)
        (fun h ↦
          ⟨affineStageReduction (affineDiagram X) (Classical.choice h),
            affineStageReductionι (affineDiagram X) (affineCocone X)
              (affineIso X) (Classical.choice h)⟩)
        (fun _ ↦ ⟨X, 𝟙 X⟩) :=
  sorry

/-- The affine reduction is the first component of `affineReductionWithι`. -/
theorem affineReduction_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    affineReduction X = (affineReductionWithι X).1 :=
  sorry

/-- The affine reduction morphism is the morphism component of
`affineReductionWithι`. -/
theorem affineReductionι_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    affineReductionι X = (affineReductionWithι X).2 :=
  sorry

/-- The chosen index type of an étale affine atlas of a formal algebraic
space. -/
def atlasIndex {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] : Type (max u v) :=
  Classical.choose ‹IsFormalAlgebraicSpace X›.exists_atlas

/-- The chosen affine charts of an étale atlas of a formal algebraic space. -/
def atlasObj {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    atlasIndex X → Sheaf (𝒮.bigTopology S) (Type (max u v)) :=
  Classical.choose (Classical.choose_spec ‹IsFormalAlgebraicSpace X›.exists_atlas)

/-- The chosen atlas maps from the affine charts into `X`. -/
def atlasπ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] : ∀ i, atlasObj X i ⟶ X :=
  Classical.choose
    (Classical.choose_spec
      (Classical.choose_spec ‹IsFormalAlgebraicSpace X›.exists_atlas))

/-- The chosen cofan of the étale affine atlas of `X`. -/
def atlasCofan {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] : Cofan (atlasObj X) :=
  Classical.choose
    (Classical.choose_spec
      (Classical.choose_spec
        (Classical.choose_spec ‹IsFormalAlgebraicSpace X›.exists_atlas)))

/-- The chosen cofan of the étale affine atlas is a colimit. -/
def atlasCofanIsColimit {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] : IsColimit (atlasCofan X) :=
  Classical.choose
    (Classical.choose_spec
      (Classical.choose_spec
        (Classical.choose_spec
          (Classical.choose_spec ‹IsFormalAlgebraicSpace X›.exists_atlas))))

/-- The chosen étale affine atlas retains affinity of charts, representability
and étaleness of the atlas maps, and joint local surjectivity. -/
theorem atlasPresentation_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    (∀ i, IsAffineFormalAlgebraicSpace (atlasObj X i)) ∧
      (∀ i, representableByAlgebraicSpaces (atlasπ X i)) ∧
        (∀ i, relativelyEtale (atlasπ X i)) ∧
          Sheaf.IsLocallySurjective
            (Cofan.IsColimit.desc (atlasCofanIsColimit X) (atlasπ X)) :=
  Classical.choose_spec
    (Classical.choose_spec
      (Classical.choose_spec
        (Classical.choose_spec
          (Classical.choose_spec ‹IsFormalAlgebraicSpace X›.exists_atlas))))

/-- Each chosen atlas chart is an affine formal algebraic space. -/
instance instIsAffineFormalAlgebraicSpace_atlasObj
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] (i : atlasIndex X) :
    IsAffineFormalAlgebraicSpace (atlasObj X i) :=
  (atlasPresentation_spec X).1 i

/-- The coproduct of the affine reductions of an étale atlas of `X`. -/
def atlasReduction {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    Sheaf (𝒮.bigTopology S) (Type (max u v)) :=
  ∐ fun i ↦ affineReduction (atlasObj X i)

/-- The induced map from the coproduct of atlas reductions into `X`. -/
def atlasReductionι {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] : atlasReduction X ⟶ X :=
  Sigma.desc fun i ↦ affineReductionι (atlasObj X i) ≫ atlasπ X i

/-- `atlasReduction X` is the coproduct of the affine reductions of the chosen
étale atlas. -/
theorem atlasReduction_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    atlasReduction X = ∐ fun i ↦ affineReduction (atlasObj X i) :=
  sorry

/-- `atlasReductionι X` is the coproduct desc of the affine reduction
inclusions followed by the atlas maps. -/
theorem atlasReductionι_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    atlasReductionι X =
      Sigma.desc fun i ↦ affineReductionι (atlasObj X i) ≫ atlasπ X i :=
  sorry

/-- The reduction of a formal algebraic space, as the coequalizer of the kernel
pair of the coproduct of atlas reductions. -/
def reduction {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    Sheaf (𝒮.bigTopology S) (Type (max u v)) :=
  coequalizer (pullback.fst (atlasReductionι X) (atlasReductionι X))
    (pullback.snd (atlasReductionι X) (atlasReductionι X))

/-- The canonical morphism from the reduction of a formal algebraic space. -/
def reductionι {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] : reduction X ⟶ X :=
  coequalizer.desc (atlasReductionι X) pullback.condition

/-- The reduction of `X` is the coequalizer of the kernel pair of
`atlasReductionι X`. -/
theorem reduction_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    reduction X =
      coequalizer (pullback.fst (atlasReductionι X) (atlasReductionι X))
        (pullback.snd (atlasReductionι X) (atlasReductionι X)) :=
  sorry

/-- The reduction morphism is the coequalizer desc of `atlasReductionι X`. -/
theorem reductionι_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    reductionι X = coequalizer.desc (atlasReductionι X) pullback.condition :=
  sorry

/-- A morphism of formal algebraic spaces induces a unique map of reductions
over it, characterized by `φ ≫ reductionι Y = reductionι X ≫ f`. -/
theorem existsUnique_mapReduction {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y) :
    ∃! φ : reduction X ⟶ reduction Y, φ ≫ reductionι Y = reductionι X ≫ f :=
  sorry

end IsFormalAlgebraicSpace

end AlgebraicGeometry
