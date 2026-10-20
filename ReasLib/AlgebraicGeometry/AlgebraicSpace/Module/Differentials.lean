module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Differentials
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.CommRingHom

/-!
# Relative differentials of a morphism of algebraic spaces

The sheaf `Ω_{X/Y}` of a morphism of algebraic spaces is the sheafification of the
relative differentials of `commInverseImageStructureSheafMap f`, the inverse-image form of
`f^♯` from `ringedToposHom f`. The universal `Y`-derivation is `d_{X/Y} : 𝒪_X ⟶ Ω_{X/Y}`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open PresheafOfModules.DifferentialsConstruction

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The underlying presheaf of an `𝒪_X`-module, as a module over the commutative
structure sheaf. -/
abbrev toCommPresheaf {X : AlgebraicSpace S} (F : X.Modules) :
    PresheafOfModules
      ((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat) :=
  (SheafOfModules.forget (structureSheaf X) ⋙
      PresheafOfModules.restrictScalars (𝟙 (structureSheaf X).obj)).obj F

/-- `toCommPresheaf F` is the `restrictScalars` image of the underlying presheaf of `F`. -/
theorem toCommPresheaf_eq {X : AlgebraicSpace S} (F : X.Modules) :
    toCommPresheaf F =
      (SheafOfModules.forget (structureSheaf X) ⋙
          PresheafOfModules.restrictScalars (𝟙 (structureSheaf X).obj)).obj F :=
  rfl

namespace Hom

/-- The type of `Y`-derivations from `𝒪_X` to an `𝒪_X`-module on the small étale site. -/
abbrev derivations {X Y : AlgebraicSpace S} (f : X ⟶ Y) (F : X.Modules) :=
  (toCommPresheaf F).Derivation' (commInverseImageStructureSheafMap f).hom

/-- `Y`-derivations into `F` are relative derivations of `commInverseImageStructureSheafMap f`. -/
theorem derivations_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) (F : X.Modules) :
    derivations f F =
      (toCommPresheaf F).Derivation' (commInverseImageStructureSheafMap f).hom :=
  rfl

/-- The sheaf of relative differentials `Ω_{X/Y}` of a morphism of algebraic spaces,
as an `𝒪_X`-module on `X_étale`. -/
def relativeDifferentials {X Y : AlgebraicSpace S} (f : X ⟶ Y) : X.Modules :=
  SheafOfModules.RingedSite.relativeDifferentials.{u + 1, u, u}
    (commInverseImageStructureSheafMap f)

/-- `Ω_{X/Y}` is the sheafification of the presheaf of Kähler differentials of
`commInverseImageStructureSheafMap f`. -/
theorem relativeDifferentials_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    relativeDifferentials f =
      (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf X).obj)).obj
        (relativeDifferentials' (commInverseImageStructureSheafMap f).hom) :=
  rfl

/-- The universal `Y`-derivation `d_{X/Y} : 𝒪_X ⟶ Ω_{X/Y}`. -/
def universalDerivation {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    derivations f (relativeDifferentials f) :=
  SheafOfModules.RingedSite.relativeDifferential.{u + 1, u, u}
    (commInverseImageStructureSheafMap f)

/-- `d_{X/Y}` is the sheafification-unit postcomposition of the presheaf-level
universal derivation of `commInverseImageStructureSheafMap f`. -/
theorem universalDerivation_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    universalDerivation f =
      (derivation' (commInverseImageStructureSheafMap f).hom).postcomp
        ((PresheafOfModules.sheafificationAdjunction.{u}
            (𝟙 (structureSheaf X).obj)).unit.app
          (relativeDifferentials' (commInverseImageStructureSheafMap f).hom)) :=
  rfl

/-- `Ω_{X/Y}` is the sheafification of the presheaf of relative differentials of the
inverse-image structure map, and forgetting commutativity of that map recovers
`(ringedToposHom f).structureMap`. -/
theorem relativeDifferentials_spec {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    relativeDifferentials f =
        (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf X).obj)).obj
          (relativeDifferentials' (commInverseImageStructureSheafMap f).hom) ∧
      (sheafCompose (smallEtaleTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map
          (commInverseImageStructureSheafMap f) =
        eqToHom (commInverseImageStructureSheaf_forget f) ≫
          (ringedToposHom f).structureMap ≫
          eqToHom (commStructureSheaf_forget X).symm :=
  sorry

/-- Morphisms out of `Ω_{X/Y}` correspond to `Y`-derivations with the same target. -/
theorem relativeDifferentials_representsDerivations {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (F : X.Modules) (D : derivations f F) :
    ∃! g : relativeDifferentials f ⟶ F,
      (universalDerivation f).postcomp
        ((SheafOfModules.forget (structureSheaf X) ⋙
            PresheafOfModules.restrictScalars (𝟙 (structureSheaf X).obj)).map g) = D :=
  sorry

end Hom

/-- `Ω[f]` is the sheaf of relative differentials `Ω_{X/Y}` of a morphism of
algebraic spaces. -/
scoped[AlgebraicGeometry.AlgebraicSpace] notation3:max "Ω[" f "]" =>
  Hom.relativeDifferentials f

/-- `d[f]` is the universal `Y`-derivation attached to a morphism of algebraic spaces. -/
scoped[AlgebraicGeometry.AlgebraicSpace] notation3:max "d[" f "]" =>
  Hom.universalDerivation f

end AlgebraicGeometry.AlgebraicSpace
