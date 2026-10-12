/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SquareZeroExtension.Module
public import ReasLib.AlgebraicGeometry.RingedSpace.Definition
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Over

/-!
# Square-zero extensions of schemes

A locally surjective square-zero extension of a scheme's structure sheaf with quasi-coherent
kernel determines a scheme and a first-order thickening. Conversely, a first-order thickening
is recovered from its inverse-image presentation sheaf.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.SquareZeroExtension

variable {S X : Scheme.{u}} [X.Over S]
variable (A : TopCat.Sheaf CommRingCat.{u} X.toTopCat)
variable (π : A ⟶ X.sheaf)
variable [hπsurj : CategoryTheory.Sheaf.IsLocallySurjective π]
variable (hπ : KernelIdeal.IsSquareZero π)

/-- The square-zero kernel, with its canonical module structure over `X.sheaf`. -/
abbrev kernelModule : X.Modules :=
  hπ.targetModule (KernelIdeal.quotientComparison_isIso π)

include hπsurj hπ in
/-- The stalks of a locally surjective square-zero extension of the structure sheaf are local
rings. -/
theorem stalk_isLocalRing (x : X) : IsLocalRing (A.presheaf.stalk x) := sorry

/-- The locally ringed space on the topological space of `X` with structure sheaf `A`. -/
def locallyRingedSpace : LocallyRingedSpace.{u} where
  toSheafedSpace :=
    { carrier := X.toTopCat
      presheaf := A.presheaf
      IsSheaf := A.2 }
  isLocalRing := stalk_isLocalRing A π hπ

variable [hqc : (kernelModule A π hπ).IsQuasicoherent]

include hqc in
/-- Quasi-coherence of the square-zero kernel gives affine neighbourhoods for the locally
ringed space defined by `A`. -/
theorem locallyRingedSpace_local_affine :
    ∀ x : locallyRingedSpace A π hπ,
      ∃ (U : OpenNhds x) (R : CommRingCat.{u}),
        Nonempty
          ((locallyRingedSpace A π hπ).restrict U.isOpenEmbedding ≅
            Spec.toLocallyRingedSpace.obj (op R)) := sorry

/-- The scheme on the topological space of `X` whose structure sheaf is `A`. -/
def scheme : Scheme.{u} where
  toLocallyRingedSpace := locallyRingedSpace A π hπ
  local_affine := locallyRingedSpace_local_affine A π hπ

/-- The underlying presheafed-space morphism from `X` to its square-zero extension. -/
def inclusionToHom :
    X.toPresheafedSpace ⟶ (locallyRingedSpace A π hπ).toPresheafedSpace where
  base := 𝟙 X.toTopCat
  c := π.hom

/-- The stalk maps of the square-zero-extension projection are local homomorphisms. -/
theorem inclusionToHom_isLocalHom (x : X) :
    IsLocalHom ((inclusionToHom A π hπ).stalkMap x).hom := sorry

/-- The locally ringed-space morphism from `X` to its square-zero extension. -/
def inclusionLRSHom :
    X.toLocallyRingedSpace ⟶ (locallyRingedSpace A π hπ) where
  toHom := inclusionToHom A π hπ
  prop := inclusionToHom_isLocalHom A π hπ

/-- The scheme morphism from `X` to the square-zero extension defined by `A`. -/
def ι : X ⟶ scheme A π hπ :=
  ⟨inclusionLRSHom A π hπ⟩

/-- The constructed morphism is a first-order thickening. -/
instance ι_isFirstOrderThickening : IsFirstOrderThickening (ι A π hπ) := sorry

/-- The inverse image of the structure sheaf of the base along the structure morphism of `X`. -/
abbrev baseSheaf (S X : Scheme.{u}) [X.Over S] :
    TopCat.Sheaf CommRingCat.{u} X.toTopCat :=
  (TopCat.Sheaf.pullback CommRingCat.{u} (X ↘ S).base).obj S.sheaf

/-- The canonical projection from the inverse image of the base structure sheaf to `X.sheaf`. -/
def baseProjection (S X : Scheme.{u}) [X.Over S] : baseSheaf S X ⟶ X.sheaf :=
  RingedSpace.Hom.inverseImageStructureSheafHomComm (X ↘ S).toShHom

variable (α : baseSheaf S X ⟶ A)
variable (hα : α ≫ π = baseProjection S X)

/-- The underlying presheafed-space map from the square-zero extension to `S`. -/
def toBaseToHom :
    (locallyRingedSpace A π hπ).toPresheafedSpace ⟶ S.toPresheafedSpace where
  base := (X ↘ S).base
  c := ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    (X ↘ S).base).homEquiv _ _) α |>.hom

include hα in
/-- The stalk maps of the morphism from the square-zero extension to `S` are local. -/
theorem toBaseToHom_isLocalHom (x : locallyRingedSpace A π hπ) :
    IsLocalHom ((toBaseToHom A π hπ α).stalkMap x).hom := sorry

/-- The structure morphism from the square-zero extension to `S`. -/
def toBase : scheme A π hπ ⟶ S :=
  ⟨{ toHom := toBaseToHom A π hπ α
     prop := toBaseToHom_isLocalHom A π hπ α hα }⟩

/-- The square-zero-extension scheme bundled as an `S`-scheme. -/
def obj : Over S :=
  Over.mk (toBase A π hπ α hα)

include hα in
/-- The square-zero-extension inclusion commutes with the structure morphisms to `S`. -/
theorem inclusion_toBase : ι A π hπ ≫ toBase A π hπ α hα = X ↘ S := sorry

/-- The first-order thickening from `X` to the square-zero extension, bundled over `S`. -/
def inclusion : X.asOver S ⟶ obj A π hπ α hα :=
  Over.homMk (ι A π hπ) (inclusion_toBase A π hπ α hα)

/-- The bundled inclusion over `S` is a first-order thickening on underlying schemes. -/
instance inclusion_isFirstOrderThickening :
    IsFirstOrderThickening (inclusion A π hπ α hα).left := sorry

end AlgebraicGeometry.Scheme.SquareZeroExtension

namespace AlgebraicGeometry.IsFirstOrderThickening

variable {S X X' : Scheme.{u}}
variable (i : X ⟶ X') [hi : IsFirstOrderThickening i]

/-- The inverse-image presentation sheaf of a first-order thickening. -/
abbrev presentationSheaf : TopCat.Sheaf CommRingCat.{u} X.toTopCat :=
  (TopCat.Sheaf.pullback CommRingCat.{u} i.base).obj X'.sheaf

/-- The canonical projection from the inverse-image presentation sheaf to `X.sheaf`. -/
def presentationProjection : presentationSheaf i ⟶ X.sheaf :=
  RingedSpace.Hom.inverseImageStructureSheafHomComm i.toShHom

include hi in
/-- The kernel of the canonical presentation of a first-order thickening is square zero. -/
theorem presentationKernel_isSquareZero :
    KernelIdeal.IsSquareZero (presentationProjection i) := sorry

include hi in
/-- The canonical presentation projection is locally surjective. -/
instance presentationProjection_isLocallySurjective :
    CategoryTheory.Sheaf.IsLocallySurjective (presentationProjection i) := sorry

/-- The square-zero kernel of the canonical presentation is quasi-coherent over `X.sheaf`. -/
instance presentationKernel_isQuasicoherent :
    (Scheme.SquareZeroExtension.kernelModule (presentationSheaf i)
      (presentationProjection i) (presentationKernel_isSquareZero i)).IsQuasicoherent := sorry

/-- Reconstruct the ambient scheme of a first-order thickening from its inverse-image structure
sheaf on `X`. -/
def reconstructedScheme : Scheme.{u} :=
  Scheme.SquareZeroExtension.scheme (presentationSheaf i) (presentationProjection i)
    (presentationKernel_isSquareZero i)

/-- The underlying presheafed-space comparison from the reconstructed scheme to `X'`. -/
def reconstructionToHom :
    (reconstructedScheme i).toPresheafedSpace ⟶ X'.toPresheafedSpace where
  base := i.base
  c := ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} i.base).unit.app
    X'.sheaf).hom

/-- The stalk maps of the reconstruction comparison are local homomorphisms. -/
theorem reconstructionToHom_isLocalHom (x : reconstructedScheme i) :
    IsLocalHom ((reconstructionToHom i).stalkMap x).hom := sorry

/-- The canonical scheme morphism from the reconstruction of a first-order thickening to its
original ambient scheme. -/
def reconstructionHom : reconstructedScheme i ⟶ X' :=
  ⟨{ toHom := reconstructionToHom i
     prop := reconstructionToHom_isLocalHom i }⟩

/-- The reconstructed inclusion agrees with the original first-order thickening after the
canonical comparison. -/
theorem inclusion_reconstructionHom :
    Scheme.SquareZeroExtension.ι (presentationSheaf i) (presentationProjection i)
        (presentationKernel_isSquareZero i) ≫ reconstructionHom i = i := sorry

variable (S : Scheme.{u}) [X.Over S] [X'.Over S] [hOver : i.IsOver S]

/-- The reconstructed ambient scheme, equipped with its canonical structure morphism to `S`. -/
def reconstructedObj : Over S :=
  Over.mk (reconstructionHom i ≫ X' ↘ S)

include hOver in
/-- The reconstructed inclusion commutes with the structure morphisms to `S`. -/
theorem reconstructedInclusion_w :
    Scheme.SquareZeroExtension.ι (presentationSheaf i) (presentationProjection i)
        (presentationKernel_isSquareZero i) ≫ (reconstructedObj i S).hom = X ↘ S := sorry

/-- The reconstructed first-order thickening, bundled as a morphism of schemes over `S`. -/
def reconstructedInclusion : X.asOver S ⟶ reconstructedObj i S :=
  Over.homMk
    (Scheme.SquareZeroExtension.ι (presentationSheaf i) (presentationProjection i)
      (presentationKernel_isSquareZero i))
    (reconstructedInclusion_w i S)

/-- The canonical reconstruction comparison commutes with the structure morphisms to `S`. -/
theorem reconstructionOverHom_w :
    reconstructionHom i ≫ (X' ↘ S) = (reconstructedObj i S).hom := sorry

/-- The canonical comparison from the reconstructed thickening to the original one over `S`. -/
def reconstructionOverHom : reconstructedObj i S ⟶ X'.asOver S :=
  Over.homMk (reconstructionHom i) (reconstructionOverHom_w i S)

/-- The canonical reconstruction comparison for a first-order thickening over `S` is an
isomorphism. -/
instance reconstructionOverHom_isIso : IsIso (reconstructionOverHom i S) := sorry

/-- Every first-order thickening over `S` is recovered from its inverse-image structure sheaf,
with its reconstructed inclusion identified with the original thickening. -/
theorem reconstruction :
    reconstructedInclusion i S ≫ reconstructionOverHom i S = i.asOver S := sorry

end AlgebraicGeometry.IsFirstOrderThickening
