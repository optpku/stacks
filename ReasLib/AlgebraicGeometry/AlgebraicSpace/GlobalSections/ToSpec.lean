module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Presentation.Descent

/-! # Canonical morphisms to spectra of global sections -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TypeCat TopCat AlgebraicGeometry
open TopologicalSpace
open AlgebraicGeometry.AlgebraicSpace

noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The scheme over `S` obtained by pulling `Spec Γ(X, 𝒪_X)` back along the unique morphism
`S ⟶ Spec ℤ`. -/
noncomputable def specGammaOver {S : Scheme.{u}} (X : AlgebraicSpace S) : Over S :=
  (Over.pullback (specULiftZIsTerminal.from S)).obj
    (overSpecZ (Spec (globalSectionsRing X)))

/-- `specGammaOver X` is the pullback of `overSpecZ (Spec (globalSectionsRing X))` along
`S ⟶ Spec ℤ`. -/
theorem specGammaOver_eq {S : Scheme.{u}} (X : AlgebraicSpace S) :
    specGammaOver X =
      (Over.pullback (specULiftZIsTerminal.from S)).obj
        (overSpecZ (Spec (globalSectionsRing X))) :=
  rfl

/-- The algebraic space over `S` representing maps to `Spec Γ(X, 𝒪_X)`. -/
noncomputable def specGamma {S : Scheme.{u}} (X : AlgebraicSpace S) : AlgebraicSpace S :=
  ofOver (specGammaOver X)

/-- `specGamma X` is the representable algebraic space attached to `specGammaOver X`. -/
theorem specGamma_eq {S : Scheme.{u}} (X : AlgebraicSpace S) :
    specGamma X = ofOver (specGammaOver X) :=
  rfl

/-- The projection from the fibre product `S ×_{Spec ℤ} Spec Γ(X, 𝒪_X)` onto `Spec Γ(X, 𝒪_X)`. -/
noncomputable def specGamma_fst {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (specGammaOver X).left ⟶ Spec (globalSectionsRing X) :=
  pullback.fst (overSpecZ (Spec (globalSectionsRing X))).hom (specULiftZIsTerminal.from S)

/-- `specGamma_fst X` is the first projection of the defining pullback. -/
theorem specGamma_fst_eq {S : Scheme.{u}} (X : AlgebraicSpace S) :
    specGamma_fst X =
      pullback.fst (overSpecZ (Spec (globalSectionsRing X))).hom
        (specULiftZIsTerminal.from S) :=
  rfl

/-- The scheme morphism from the chosen atlas of `X` to `Spec Γ(X, 𝒪_X)` classified by the
equalizer inclusion `Γ(X, 𝒪_X) ⟶ Γ(U, 𝒪_U)`. -/
noncomputable def atlasToSpec_scheme {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (chosenPresentation X).U.left ⟶ Spec (globalSectionsRing X) :=
  (chosenPresentation X).U.left.toSpecΓ ≫ Spec.map (globalSectionsRing_ι X)

/-- `atlasToSpec_scheme X` is `U.toSpecΓ` followed by `Spec.map` of the equalizer inclusion. -/
theorem atlasToSpec_scheme_eq {S : Scheme.{u}} (X : AlgebraicSpace S) :
    atlasToSpec_scheme X =
      (chosenPresentation X).U.left.toSpecΓ ≫ Spec.map (globalSectionsRing_ι X) :=
  rfl

/-- The atlas morphism to `Spec Γ(X, 𝒪_X)` is a morphism over `Spec ℤ`. -/
theorem atlasToSpec_scheme_w {S : Scheme.{u}} (X : AlgebraicSpace S) :
    atlasToSpec_scheme X ≫ (overSpecZ (Spec (globalSectionsRing X))).hom =
      ((Over.map (specULiftZIsTerminal.from S)).obj (chosenPresentation X).U).hom :=
  sorry

/-- The atlas of `X`, viewed over `Spec ℤ`, as a morphism to `Spec Γ(X, 𝒪_X)`. -/
noncomputable def atlasToSpec_overSpecZ {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (Over.map (specULiftZIsTerminal.from S)).obj (chosenPresentation X).U ⟶
      overSpecZ (Spec (globalSectionsRing X)) :=
  Over.homMk (atlasToSpec_scheme X) (atlasToSpec_scheme_w X)

/-- The underlying scheme morphism of `atlasToSpec_overSpecZ X` is `atlasToSpec_scheme X`. -/
theorem atlasToSpec_overSpecZ_left {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (atlasToSpec_overSpecZ X).left = atlasToSpec_scheme X :=
  rfl

/-- The morphism in `Over S` from the chosen atlas to `specGammaOver X`, obtained by the
`Over.map ⊣ Over.pullback` adjunction. -/
noncomputable def atlasToSpecGammaOver {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (chosenPresentation X).U ⟶ specGammaOver X :=
  ((Over.mapPullbackAdj (specULiftZIsTerminal.from S)).homEquiv
      (chosenPresentation X).U (overSpecZ (Spec (globalSectionsRing X))))
    (atlasToSpec_overSpecZ X)

/-- `atlasToSpecGammaOver X` is the mate of `atlasToSpec_overSpecZ X`. -/
theorem atlasToSpecGammaOver_eq {S : Scheme.{u}} (X : AlgebraicSpace S) :
    atlasToSpecGammaOver X =
      ((Over.mapPullbackAdj (specULiftZIsTerminal.from S)).homEquiv
          (chosenPresentation X).U (overSpecZ (Spec (globalSectionsRing X))))
        (atlasToSpec_overSpecZ X) :=
  rfl

/-- The morphism of algebraic spaces from the presenting scheme to `specGamma X`. -/
noncomputable def atlasToSpecGamma {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ofOver (chosenPresentation X).U ⟶ specGamma X :=
  ofOverMap (atlasToSpecGammaOver X)

/-- `atlasToSpecGamma X` is `ofOverMap` of `atlasToSpecGammaOver X`. -/
theorem atlasToSpecGamma_eq {S : Scheme.{u}} (X : AlgebraicSpace S) :
    atlasToSpecGamma X = ofOverMap (atlasToSpecGammaOver X) :=
  rfl

/-- The two relation projections equalize `atlasToSpecGamma X`. -/
theorem atlasToSpecGamma_equalizes {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ofOverMap (chosenPresentation X).R.t ≫ atlasToSpecGamma X =
      ofOverMap (chosenPresentation X).R.s ≫ atlasToSpecGamma X :=
  sorry

/-- The graph of the absolute canonical map `X → Spec Γ(X, O_X)`, as a map
over `S` into the product with `S`. It is obtained by descending the atlas map;
direct image along this graph alone is not direct image to `Spec Γ(X, O_X)`. -/
noncomputable def toSpecGamma {S : Scheme.{u}} (X : AlgebraicSpace S) : X ⟶ specGamma X :=
  Presentation.homDesc (chosenPresentation X) (atlasToSpecGamma X)
    (atlasToSpecGamma_equalizes X)

/-- `toSpecGamma X` is the descent of `atlasToSpecGamma X` along the chosen presentation. -/
theorem toSpecGamma_eq {S : Scheme.{u}} (X : AlgebraicSpace S) :
    toSpecGamma X =
      Presentation.homDesc (chosenPresentation X) (atlasToSpecGamma X)
        (atlasToSpecGamma_equalizes X) :=
  rfl

/-- The first projection of `specGammaOver X` is a morphism over `Spec ℤ`. -/
theorem specGammaComparison_w (X : AlgebraicSpace specZ) :
    specGamma_fst X ≫ (overSpecZ (Spec (globalSectionsRing X))).hom =
      (specGammaOver X).hom :=
  sorry

/-- Over `Spec ℤ`, the comparison from `specGamma X` to the affine algebraic space
`ofOver (overSpecZ (Spec Γ(X, 𝒪_X)))`. -/
noncomputable def specGammaComparison (X : AlgebraicSpace specZ) :
    specGamma X ⟶ ofOver (overSpecZ (Spec (globalSectionsRing X))) :=
  ofOverMap (Over.homMk (specGamma_fst X) (specGammaComparison_w X))

/-- Over `Spec ℤ`, `toSpecGamma` recovers `GlobalSections.homMk` of `Scheme.ΓSpecIso`. -/
theorem toSpecGamma_specZ (X : AlgebraicSpace specZ) :
    toSpecGamma X ≫ specGammaComparison X =
      GlobalSections.homMk (Scheme.ΓSpecIso (globalSectionsRing X)).hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
