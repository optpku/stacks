module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.FiberedCategory.HomLift
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.MapsIntoAffineOpen
public import ReasLib.RingTheory.RingHom.SquareZero.Map
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import ReasLib.AlgebraicGeometry.Deformation.SquareZero

/-!
# Objects over spectra and square-zero deformation situations

Objects over affine spectra, their square-zero deformation situations, lifts,
and the induced maps on kernel modules.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} [IsLocallyNoetherian S]

namespace Spectrum

/-- An object of `X` over `Spec(A) → S` for an `S`-algebra whose spectrum maps
into an affine open of `S`. -/
structure ObjectOverSpec (X : GroupoidsOver S) extends CommRingCat.{u} where
  /-- Structure morphism `Spec(A) ⟶ S`. -/
  toS : Spec toCommRingCat ⟶ S
  /-- `Spec(A) ⟶ S` factors through an affine open of `S`. -/
  mapsIntoAffineOpen : toS.MapsIntoAffineOpen
  /-- The object `x` of the total category of `X`. -/
  obj : X.total
  /-- `x` lies over `Spec(A) ⟶ S`. -/
  over_obj : X.p.obj obj = Over.mk toS

/-- The fiber object over the structure morphism of an object over a spectrum. -/
def ObjectOverSpec.toFiber {X : GroupoidsOver S} (ξ : ObjectOverSpec X) :
    X.p.Fiber (Over.mk ξ.toS) :=
  Functor.Fiber.mk ξ.over_obj

end Spectrum

/-- An object over an affine spectrum whose structure morphism maps into an affine open. -/
abbrev ObjectOverSpec (X : GroupoidsOver S) := Spectrum.ObjectOverSpec X

namespace ObjectOverSpec

variable {X : GroupoidsOver S}

/-- The underlying type of the coefficient ring of an object over a spectrum. -/
abbrev carrier (ξ : ObjectOverSpec X) : Type u := ξ.toCommRingCat.carrier

/-- The canonical commutative ring structure on the coefficient ring. -/
abbrev commRing (ξ : ObjectOverSpec X) : CommRing ξ.carrier := ξ.toCommRingCat.commRing

/-- The coefficient ring as a bundled commutative ring. -/
abbrev ring (ξ : ObjectOverSpec X) : CommRingCat.{u} := ξ.toCommRingCat

/-- The underlying total-category object of an object over a spectrum. -/
abbrev obj (ξ : ObjectOverSpec X) : X.total := Spectrum.ObjectOverSpec.obj ξ

/-- Package a ring, a structure morphism into an affine open, and an object over
its spectrum. -/
def of (carrier : Type u) [CommRing carrier]
    (toS : Spec (CommRingCat.of carrier) ⟶ S) (mapsIntoAffineOpen : toS.MapsIntoAffineOpen)
    (obj : X.total) (over_obj : X.p.obj obj = Over.mk toS) :
    ObjectOverSpec X where
  toCommRingCat := CommRingCat.of carrier
  toS := toS
  mapsIntoAffineOpen := mapsIntoAffineOpen
  obj := obj
  over_obj := over_obj

/-- An `ObjectOverSpec` is an object over `Spec(A) ⟶ S` mapping into an affine
open. -/
theorem spec (ξ : ObjectOverSpec X) :
    ξ.toS.MapsIntoAffineOpen ∧ X.p.obj ξ.obj = Over.mk ξ.toS :=
  sorry

/-- The morphism `Spec(B) ⟶ Spec(A)` over `S` induced by a ring map compatible
with the structure morphisms. -/
def specOverMap {ξ η : ObjectOverSpec X} (toRingHom : ξ.carrier →+* η.carrier)
    (toS_comp : Spec.map (CommRingCat.ofHom toRingHom) ≫ ξ.toS = η.toS) :
    Over.mk η.toS ⟶ Over.mk ξ.toS :=
  Over.homMk (Spec.map (CommRingCat.ofHom toRingHom)) toS_comp

/-- A morphism of objects over spectra along `A → B`, with restriction arrow
`y ⟶ x` over `Spec(B) ⟶ Spec(A)`. -/
structure Hom (ξ η : ObjectOverSpec X) where
  /-- Underlying ring homomorphism `A → B`. -/
  toRingHom : ξ.carrier →+* η.carrier
  /-- `Spec(B) ⟶ Spec(A) ⟶ S` recovers the structure map of the target. -/
  toS_comp : Spec.map (CommRingCat.ofHom toRingHom) ≫ ξ.toS = η.toS
  /-- Restriction arrow `y ⟶ x` in the total category. -/
  restriction : η.obj ⟶ ξ.obj
  /-- The restriction arrow lies over `Spec.map` of the ring homomorphism. -/
  isHomLift : X.p.IsHomLift (specOverMap toRingHom toS_comp) restriction

/-- Package a ring map, a triangle over `S`, and a restriction arrow as a
morphism of objects over spectra. -/
def Hom.of {ξ η : ObjectOverSpec X} (toRingHom : ξ.carrier →+* η.carrier)
    (toS_comp : Spec.map (CommRingCat.ofHom toRingHom) ≫ ξ.toS = η.toS)
    (restriction : η.obj ⟶ ξ.obj)
    (isHomLift : X.p.IsHomLift (ObjectOverSpec.specOverMap toRingHom toS_comp) restriction) :
    Hom ξ η where
  toRingHom := toRingHom
  toS_comp := toS_comp
  restriction := restriction
  isHomLift := isHomLift

/-- A morphism of objects over spectra is a ring map `A → B` together with a
restriction arrow `y ⟶ x` over `Spec(B) ⟶ Spec(A)`. -/
theorem Hom.spec {ξ η : ObjectOverSpec X} (f : Hom ξ η) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ ξ.toS = η.toS ∧
      X.p.IsHomLift (specOverMap f.toRingHom f.toS_comp) f.restriction :=
  sorry

/-- The morphism `Spec(B) ⟶ Spec(A)` over `S` induced by a morphism of objects
over spectra. -/
def Hom.overMap {ξ η : ObjectOverSpec X} (f : Hom ξ η) :
    Over.mk η.toS ⟶ Over.mk ξ.toS :=
  specOverMap f.toRingHom f.toS_comp

/-- `Hom.overMap` is `Spec` of the stored ring homomorphism. -/
theorem Hom.overMap_left {ξ η : ObjectOverSpec X} (f : Hom ξ η) :
    (Hom.overMap f).left = Spec.map (CommRingCat.ofHom f.toRingHom) :=
  sorry

/-- Identity morphism of an object over a spectrum. -/
def Hom.id (ξ : ObjectOverSpec X) : Hom ξ ξ where
  toRingHom := RingHom.id ξ.carrier
  toS_comp := sorry
  restriction := 𝟙 ξ.obj
  isHomLift := sorry

/-- Composition of morphisms of objects over spectra, covariant in `A → B`. -/
def Hom.comp {ξ η ζ : ObjectOverSpec X} (f : Hom ξ η) (g : Hom η ζ) : Hom ξ ζ where
  toRingHom := g.toRingHom.comp f.toRingHom
  toS_comp := sorry
  restriction := g.restriction ≫ f.restriction
  isHomLift := sorry

end ObjectOverSpec

/-- A deformation situation `(x, A' → A)`: a square-zero surjection of
`S`-algebras together with an object of `X` over `Spec(A)`. -/
structure DeformationSituation (X : GroupoidsOver S) extends ObjectOverSpec X where
  /-- Source ring `A'` of the square-zero extension. -/
  sourceRing : CommRingCat.{u}
  /-- Square-zero surjection `A' → A`. -/
  extension : RingHom.SquareZeroExtension.Map sourceRing toCommRingCat
  /-- Structure morphism `Spec(A') ⟶ S`. -/
  sourceToS : Spec sourceRing ⟶ S
  /-- `Spec(A) ⟶ Spec(A') ⟶ S` recovers the structure map of `A`. -/
  toS_comp : Spec.map (CommRingCat.ofHom extension.hom) ≫ sourceToS = toS

namespace DeformationSituation

variable {X : GroupoidsOver S}

/-- The underlying type of the source ring of a deformation situation. -/
abbrev source (σ : DeformationSituation X) : Type u := σ.sourceRing

/-- The ring homomorphism defining the square-zero extension. -/
abbrev toCarrier (σ : DeformationSituation X) : σ.source →+* σ.carrier :=
  σ.extension.hom

/-- The extension map of a deformation situation is a square-zero extension. -/
theorem isSquareZero (σ : DeformationSituation X) : σ.toCarrier.IsSquareZeroExtension :=
  σ.extension.property

/-- Package a square-zero extension of `S`-algebras and an object over
`Spec(A)` as a deformation situation. -/
def of (carrier source : Type u) [CommRing carrier] [CommRing source]
    (toS : Spec (CommRingCat.of carrier) ⟶ S) (mapsIntoAffineOpen : toS.MapsIntoAffineOpen)
    (obj : X.total) (over_obj : X.p.obj obj = Over.mk toS)
    (toCarrier : source →+* carrier) [toCarrier.IsSquareZeroExtension]
    (sourceToS : Spec (CommRingCat.of source) ⟶ S)
    (toS_comp : Spec.map (CommRingCat.ofHom toCarrier) ≫ sourceToS = toS) :
    DeformationSituation X where
  toCommRingCat := CommRingCat.of carrier
  toS := toS
  mapsIntoAffineOpen := mapsIntoAffineOpen
  obj := obj
  over_obj := over_obj
  sourceRing := CommRingCat.of source
  extension := RingHom.SquareZeroExtension.Map.of toCarrier
  sourceToS := sourceToS
  toS_comp := toS_comp

/-- A deformation situation is a square-zero surjection `A' → A` together with
an object over `Spec(A) ⟶ S` mapping into an affine open. -/
theorem spec (σ : DeformationSituation X) :
    σ.toS.MapsIntoAffineOpen ∧ σ.toCarrier.IsSquareZeroExtension ∧
      X.p.obj σ.obj = Over.mk σ.toS ∧
        Spec.map (CommRingCat.ofHom σ.toCarrier) ≫ σ.sourceToS = σ.toS :=
  sorry

/-- The kernel `I = Ker(A' → A)` as an `A`-module. -/
def kernelModule (σ : DeformationSituation X) : ModuleCat.{u} σ.carrier :=
  ModuleCat.of σ.carrier (RingHom.ker σ.toCarrier)

/-- `kernelModule` is the kernel of the stored square-zero extension, as an
object of `ModuleCat A`. -/
theorem kernelModule_obj (σ : DeformationSituation X) :
    σ.kernelModule = ModuleCat.of σ.carrier (RingHom.ker σ.toCarrier) :=
  sorry

/-- The kernel ideal of a deformation situation has square zero. -/
theorem ker_sq_eq_bot (σ : DeformationSituation X) :
    RingHom.ker σ.toCarrier ^ 2 = ⊥ :=
  sorry

/-- The thickening `Spec(A) ⟶ Spec(A')` over `S`. -/
def thickening (σ : DeformationSituation X) :
    Over.mk σ.toS ⟶ Over.mk σ.sourceToS :=
  Over.homMk (Spec.map (CommRingCat.ofHom σ.toCarrier)) σ.toS_comp

/-- A lift of `x` along the thickening `Spec(A) ⟶ Spec(A')`. -/
structure ObjectLift (σ : DeformationSituation X) where
  /-- The lifted object `x'` over `Spec(A')`. -/
  obj' : X.total
  /-- The arrow `x ⟶ x'` in the total category. -/
  hom : σ.obj ⟶ obj'
  /-- The arrow lies over `Spec.map (A' → A)`. -/
  isHomLift : X.p.IsHomLift (thickening σ) hom

/-- Package a total-category arrow over `Spec(A) ⟶ Spec(A')` as a lift of a
deformation situation. -/
def ObjectLift.of (σ : DeformationSituation X) (obj' : X.total) (hom : σ.obj ⟶ obj')
    (isHomLift : X.p.IsHomLift
      (thickening σ) hom) :
    ObjectLift σ where
  obj' := obj'
  hom := hom
  isHomLift := isHomLift

/-- An object lift is an arrow `x ⟶ x'` over `Spec(A) ⟶ Spec(A')`. -/
theorem ObjectLift.spec {σ : DeformationSituation X} (ℓ : ObjectLift σ) :
    X.p.IsHomLift (thickening σ) ℓ.hom :=
  sorry

/-- A morphism of deformation situations, covariant in `A → B`: ring maps
`A → B` and `A' → B'` making the square commute, together with a restriction
arrow `y ⟶ x` over `Spec(B) ⟶ Spec(A)`. -/
structure Hom (σ τ : DeformationSituation X)
    extends ObjectOverSpec.Hom σ.toObjectOverSpec τ.toObjectOverSpec where
  /-- Ring homomorphism `A' → B'` of the square-zero sources. -/
  toSourceHom : σ.source →+* τ.source
  /-- `Spec(B') ⟶ Spec(A') ⟶ S` recovers the structure map of `B'`. -/
  sourceToS_comp : Spec.map (CommRingCat.ofHom toSourceHom) ≫ σ.sourceToS = τ.sourceToS
  /-- The square `A' → B'`, `A' → A`, `B' → B`, `A → B` commutes. -/
  commSq : τ.toCarrier.comp toSourceHom = toRingHom.comp σ.toCarrier

/-- Package ring maps of sources and targets, the commuting square, and a
restriction arrow as a morphism of deformation situations. -/
def Hom.of {σ τ : DeformationSituation X} (toRingHom : σ.carrier →+* τ.carrier)
    (toS_comp : Spec.map (CommRingCat.ofHom toRingHom) ≫ σ.toS = τ.toS)
    (restriction : τ.obj ⟶ σ.obj)
    (isHomLift : X.p.IsHomLift (ObjectOverSpec.specOverMap toRingHom toS_comp) restriction)
    (toSourceHom : σ.source →+* τ.source)
    (sourceToS_comp : Spec.map (CommRingCat.ofHom toSourceHom) ≫ σ.sourceToS = τ.sourceToS)
    (commSq : τ.toCarrier.comp toSourceHom = toRingHom.comp σ.toCarrier) :
    Hom σ τ where
  toRingHom := toRingHom
  toS_comp := toS_comp
  restriction := restriction
  isHomLift := isHomLift
  toSourceHom := toSourceHom
  sourceToS_comp := sourceToS_comp
  commSq := commSq

/-- A morphism of deformation situations is a commuting square of square-zero
extensions together with a restriction arrow over `Spec(B) ⟶ Spec(A)`. -/
theorem Hom.spec {σ τ : DeformationSituation X} (f : Hom σ τ) :
    τ.toCarrier.comp f.toSourceHom = f.toRingHom.comp σ.toCarrier ∧
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ σ.toS = τ.toS ∧
        X.p.IsHomLift (ObjectOverSpec.specOverMap f.toRingHom f.toS_comp) f.restriction :=
  sorry

/-- The image of a kernel element under the source ring map of a morphism of
deformation situations remains in the kernel. -/
theorem Hom.kernelMap_mem {σ τ : DeformationSituation X} (f : Hom σ τ)
    (x : RingHom.ker σ.toCarrier) :
    f.toSourceHom x.1 ∈ RingHom.ker τ.toCarrier :=
  sorry

/-- The `A`-linear map `Ker(A' → A) → Ker(B' → B)` induced by a morphism of
deformation situations. -/
def Hom.kernelMap {σ τ : DeformationSituation X} (f : Hom σ τ) :
    σ.kernelModule ⟶ (ModuleCat.restrictScalars f.toRingHom).obj τ.kernelModule :=
  ConcreteCategory.ofHom
    { toFun := fun x ↦ ⟨f.toSourceHom x.1, Hom.kernelMap_mem f x⟩
      map_add' := sorry
      map_smul' := sorry }

/-- `kernelMap` sends a kernel element to its image under the source ring map. -/
theorem Hom.kernelMap_apply {σ τ : DeformationSituation X} (f : Hom σ τ)
    (x : σ.kernelModule) :
    f.kernelMap x = ⟨f.toSourceHom x.1, Hom.kernelMap_mem f x⟩ :=
  sorry

end DeformationSituation

end AlgebraicGeometry.GroupoidsOver
